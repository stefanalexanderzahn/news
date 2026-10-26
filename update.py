#!/usr/bin/env python3
"""News-Dashboard: holt die Quellen aus sources.json, sammelt eine Historie,
bildet quellenübergreifende Top-10-Listen (24 Stunden, 7 Tage, 30 Tage),
übersetzt fremdsprachige Überschriften ins Deutsche und sammelt Trendlisten.

Nur Python-Standardbibliothek, keine Installation nötig.
Optional: Geheimnis DEEPL_API_KEY (GitHub -> Settings -> Secrets) für bessere Übersetzungen.
"""
import argparse
import email.utils
import hashlib
import html
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path

UA = "Mozilla/5.0 (compatible; NewsDashboard/1.0)"
WIKI_UA = "NewsDashboard/1.0 (private news overview; https://github.com/stefanalexanderzahn/news)"
WINDOWS = {"24h": 24, "7d": 24 * 7, "30d": 24 * 30}
REGIONS = ("de", "eu", "world")
KEEP_DAYS = 35
TOP_N = 10
SIM_THRESHOLD = 0.5
MAX_NEW_TRANSLATIONS = 150      # pro Lauf; Rest kommt beim nächsten Lauf
PAUSE = float(os.environ.get("TRANSLATE_PAUSE", "0.3"))

STOP = set(
    """der die das den dem des ein eine einer einem einen eines und oder aber mit von für auf aus bei
    nach über unter vor zum zur im in am an ist sind war waren wird werden wurde wurden hat haben hatte
    nicht auch noch nur wie als dass sich sein ihre ihr ihren kann können soll sollen will wollen muss
    müssen mehr neue neuer neues gegen ohne sagt warum wer was wann wo wegen durch bis seit zwischen
    jetzt heute gibt geben geht gehen the and for with from that this are was were has have not you
    your new says will its into over after about""".split()
)

# Hauptseiten der Wikipedia-Sprachversionen (stehen sonst immer auf Platz 1)
WIKI_MAIN = {
    "main_page", "hauptseite", "pagina_principale", "portada", "strona_główna", "hoofdpagina",
    "pagina_principal", "заглавная_страница", "メインページ", "首页", "anasayfa", "forside",
    "startsida", "etusivu", "-",
}
# einfacher Jugendschutz-Filter für die Wikipedia-Listen
WIKI_BLOCK = ("porn", "xxx", "xvideo", "xnxx", "hentai", "onlyfans", "erotic")


# ----------------------------------------------------------------- Hilfsfunktionen
def now_utc():
    return datetime.now(timezone.utc)


def iso(d):
    return d.astimezone(timezone.utc).isoformat(timespec="seconds")


def load_json(path, default):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return default


class HttpFail(RuntimeError):
    def __init__(self, code, msg):
        super().__init__(msg)
        self.code = code


def fetch(url, timeout=25, headers=None, data=None):
    hdrs = {"User-Agent": UA, "Accept": "*/*"}
    if headers:
        hdrs.update(headers)
    req = urllib.request.Request(url, data=data, headers=hdrs)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.read()
    except urllib.error.HTTPError as exc:
        try:
            snippet = clean(exc.read(400).decode("utf-8", "replace"))[:70]
        except Exception:
            snippet = ""
        raise HttpFail(exc.code, "HTTP %d%s%s" % (exc.code, (" " + str(exc.reason)) if exc.reason else "", (" – " + snippet) if snippet else ""))


def describe(exc):
    """Kurze, verständliche Fehlermeldung für die Statusanzeige."""
    if isinstance(exc, (HttpFail, ValueError)):
        return str(exc)[:150]
    return "%s: %s" % (type(exc).__name__, str(exc)[:110])


def local(tag):
    return tag.rsplit("}", 1)[-1]


def clean(text):
    text = html.unescape(text or "")
    text = re.sub(r"<[^>]+>", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def safe_link(url):
    url = (url or "").strip()
    return url if url.startswith(("http://", "https://")) else ""


def parse_date(s):
    if not s:
        return None
    s = s.strip()
    d = None
    try:
        d = email.utils.parsedate_to_datetime(s)
    except Exception:
        d = None
    if d is None:
        try:
            d = datetime.fromisoformat(s.replace("Z", "+00:00"))
        except Exception:
            return None
    if d.tzinfo is None:
        d = d.replace(tzinfo=timezone.utc)
    return d.astimezone(timezone.utc)


IMG_EXT = (".jpg", ".jpeg", ".png", ".webp", ".gif", ".avif")


def good_image(url):
    """Nur https-Bilder (sonst blockiert der Browser sie auf einer https-Seite)."""
    url = html.unescape((url or "").strip())
    return url if url.startswith("https://") and len(url) < 600 else ""


def find_image(el):
    """Sucht in einem RSS-/Atom-Eintrag nach einem Vorschaubild."""
    thumbs, contents, encl, inline = [], [], [], []
    for sub in el.iter():
        name = local(sub.tag)
        url = sub.get("url") or ""
        typ = (sub.get("type") or "").lower()
        if name == "thumbnail" and url:
            thumbs.append(url)
        elif name == "content" and url and (sub.get("medium") == "image" or typ.startswith("image") or url.lower().split("?")[0].endswith(IMG_EXT)):
            contents.append(url)
        elif name == "enclosure" and url and (typ.startswith("image") or url.lower().split("?")[0].endswith(IMG_EXT)):
            encl.append(url)
        elif name == "link" and sub.get("rel") == "enclosure" and sub.get("href") and typ.startswith("image"):
            encl.append(sub.get("href"))
        elif name in ("description", "encoded", "summary", "content") and sub.text:
            m = re.search(r"<img[^>]+src=[\"']([^\"']+)", html.unescape(sub.text), flags=re.I)
            if m:
                inline.append(m.group(1))
    for url in thumbs + contents + encl + inline:
        ok = good_image(url)
        if ok:
            return ok
    return ""


def _parse_feed_xml(data):
    """RSS 2.0 und Atom -> Liste aus {title, link, date, image, src}."""
    root = ET.fromstring(data)
    if local(root.tag).lower() not in ("rss", "feed", "rdf", "channel"):
        raise ValueError("Kein Feed – Antwort beginnt mit: %s" % (clean(data[:300].decode("utf-8", "replace"))[:70] or "(leer)"))
    out = []
    for el in root.iter():
        if local(el.tag) not in ("item", "entry"):
            continue
        d = {}
        for ch in el:
            name = local(ch.tag)
            if name == "title":
                d["title"] = clean(ch.text)
            elif name == "link":
                href = ch.get("href")
                if href and ch.get("rel") in (None, "alternate"):
                    d.setdefault("link", href)
                elif ch.text and ch.text.strip():
                    d.setdefault("link", ch.text.strip())
            elif name in ("pubDate", "published", "updated", "date"):
                d.setdefault("date", ch.text)
            elif name == "source":
                d.setdefault("src", clean(ch.text))
        if d.get("title"):
            out.append(
                {
                    "title": d["title"],
                    "link": safe_link(d.get("link")),
                    "date": parse_date(d.get("date")),
                    "image": find_image(el),
                    "src": d.get("src", ""),
                }
            )
    return out


def _parse_feed_lenient(data):
    """Notlösung für Feeds mit kleinen XML-Fehlern (z. B. loses &-Zeichen)."""
    text = data.decode("utf-8", errors="replace")
    out = []
    for block in re.findall(r"<(?:item|entry)[ >].*?</(?:item|entry)>", text, flags=re.S | re.I):

        def tag(name):
            m = re.search(r"<%s(?:\s[^>]*)?>(.*?)</%s>" % (name, name), block, flags=re.S | re.I)
            if not m:
                return ""
            v = m.group(1).strip()
            c = re.match(r"<!\[CDATA\[(.*?)\]\]>$", v, flags=re.S)
            return c.group(1) if c else v

        title = clean(tag("title"))
        link = tag("link")
        if not link:
            m = re.search(r'<link[^>]*href="([^"]+)"', block, flags=re.I)
            link = m.group(1) if m else ""
        date = tag("pubDate") or tag("published") or tag("updated") or tag("dc:date")
        image = ""
        for pat in (r'<media:thumbnail[^>]*url="([^"]+)"', r'<media:content[^>]*url="([^"]+)"',
                    r'<enclosure[^>]*url="([^"]+)"[^>]*type="image', r'<img[^>]+src=["\']([^"\']+)'):
            m = re.search(pat, block, flags=re.I)
            if m and good_image(m.group(1)):
                image = good_image(m.group(1))
                break
        if title:
            out.append({"title": title, "link": safe_link(html.unescape(link)), "date": parse_date(date),
                        "image": image, "src": clean(tag("source"))})
    if not out:
        raise ValueError("Feed nicht lesbar")
    return out


def parse_feed(data):
    try:
        return _parse_feed_xml(data)
    except ET.ParseError:
        try:
            return _parse_feed_lenient(data)
        except ValueError:
            start = clean(data[:300].decode("utf-8", "replace"))[:70]
            raise ValueError("Kein lesbarer Feed – Antwort beginnt mit: %s" % (start or "(leer)"))


def google_news_url(src):
    """Ersatzweg für Seiten ohne (funktionierenden) Feed: Google-News-Suche nach der Domain."""
    if src.get("url"):
        return src["url"]
    q = src.get("query") or ("site:" + src["site"])
    q += " when:" + src.get("when", "7d")
    if src.get("lang", "de") == "de":
        hl, gl, ceid = "de", "DE", "DE:de"
    else:
        hl, gl, ceid = "en-US", "US", "US:en"
    return "https://news.google.com/rss/search?q=%s&hl=%s&gl=%s&ceid=%s" % (urllib.parse.quote_plus(q, safe=":"), hl, gl, ceid)


def strip_suffix(title, source_name):
    """Google News hängt ' - Quellenname' an jede Überschrift."""
    if source_name:
        for sep in (" - ", " – ", " — "):
            suffix = sep + source_name
            if title.endswith(suffix):
                return title[: -len(suffix)].rstrip()
    return title


def load_entries(src):
    if src.get("type") == "googlenews":
        entries = parse_feed(fetch(google_news_url(src)))
        for e in entries:
            e["title"] = strip_suffix(e["title"], e.get("src"))
        return entries
    return parse_feed(fetch(src["url"]))


# ----------------------------------------------------------------- Nachrichten / Payments
def update_history(history, category, source, entries, now):
    added = 0
    for e in entries:
        key = hashlib.sha1((category + "|" + (e["link"] or e["title"])).encode()).hexdigest()[:16]
        if key in history:
            if e.get("image") and not history[key].get("image"):
                history[key]["image"] = e["image"]
            continue
        pub = e["date"]
        if pub and pub > now + timedelta(hours=1):
            pub = now
        history[key] = {
            "title": e["title"],
            "link": e["link"],
            "source": source,
            "category": category,
            "published": iso(pub) if pub else None,
            "first_seen": iso(now),
            "image": e.get("image", ""),
        }
        added += 1
    return added


def effective_time(item):
    return datetime.fromisoformat(item["published"] or item["first_seen"])


def tokens(title):
    """Wörter ohne Füllwörter; auf 7 Buchstaben gekürzt, damit 'Kanzler'/'Kanzlers' und
    'digitale'/'digitaler' als gleich gelten."""
    words = re.findall(r"[a-zäöüß0-9]{3,}", title.lower())
    return frozenset(w[:7] for w in words if w not in STOP)


def cluster(items):
    """Gruppiert Meldungen mit ähnlicher Überschrift. Gibt Liste von Index-Listen zurück.
    Eine Meldung gehört zu einem Thema, wenn sie mindestens 2 Wörter und mindestens die
    Hälfte ihrer Wörter mit den bisherigen Meldungen des Themas teilt."""
    n = len(items)
    freq = Counter(t for it in items for t in it["tok"])
    too_common = {t for t, c in freq.items() if c > max(40, n * 0.05)}
    postings = defaultdict(set)      # Wort -> Themen-Nummern
    topic_tok = []                   # Themen-Nummer -> alle Wörter des Themas
    clusters = []
    for i, it in enumerate(items):
        toks = [t for t in it["tok"] if t not in too_common]
        shared = Counter()
        for t in toks:
            for cid in postings[t]:
                shared[cid] += 1
        best, best_ratio = None, 0.0
        for cid, c in shared.items():
            if c < 2:
                continue
            ratio = len(it["tok"] & topic_tok[cid]) / max(1, len(it["tok"]))
            if ratio >= SIM_THRESHOLD and ratio > best_ratio:
                best, best_ratio = cid, ratio
        if best is None:
            best = len(clusters)
            clusters.append([])
            topic_tok.append(set())
        clusters[best].append(i)
        topic_tok[best] |= it["tok"]
        for t in toks:
            postings[t].add(best)
    return clusters


def top_stories(items, now, hours, weights, order):
    cutoff = now - timedelta(hours=hours)
    win = [it for it in items if it["time"] >= cutoff]
    if not win:
        return []
    win.sort(key=lambda it: it["time"], reverse=True)
    stories = []
    for idxs in cluster(win):
        members = [win[k] for k in idxs]
        per_source = {}
        for m in members:
            cur = per_source.get(m["source"])
            if cur is None or m["time"] > cur["time"]:
                per_source[m["source"]] = m
        newest = max(m["time"] for m in members)
        age_h = (now - newest).total_seconds() / 3600
        score = (
            sum(weights.get(s, 1) for s in per_source) * 100
            + max(0.0, 10 * (1 - age_h / hours))
            + min(len(members), 5) * 0.5
        )
        lead = min(per_source.values(), key=lambda m: (-weights.get(m["source"], 1), order.get(m["source"], 99)))
        with_img = [m for m in sorted(members, key=lambda m: (m["source"] != lead["source"], -m["time"].timestamp())) if m.get("image")]
        stories.append(
            {
                "score": score,
                "title": lead["title"],
                "lang": lead.get("lang", "de"),
                "link": lead["link"],
                "image": with_img[0]["image"] if with_img else "",
                "n_sources": len(per_source),
                "time": iso(newest),
                "sources": [
                    {"name": s, "title": m["title"], "link": m["link"]}
                    for s, m in sorted(per_source.items(), key=lambda kv: order.get(kv[0], 99))
                ],
            }
        )
    stories.sort(key=lambda s: s["score"], reverse=True)
    for s in stories:
        del s["score"]
    return stories[:TOP_N]


# ----------------------------------------------------------------- Trends / Social
def fetch_googletrends(src):
    geo = src.get("geo", "DE")
    root = ET.fromstring(fetch(src.get("url") or "https://trends.google.com/trending/rss?geo=" + geo))
    out = []
    for item in root.iter():
        if local(item.tag) != "item":
            continue
        title, traffic, link = "", "", ""
        for ch in item:
            name = local(ch.tag)
            if name == "title":
                title = clean(ch.text)
            elif name == "approx_traffic":
                traffic = clean(ch.text)
            elif name == "news_item" and not link:
                for g in ch:
                    if local(g.tag) == "news_item_url":
                        link = safe_link(g.text)
        if title:
            if not link:
                link = "https://trends.google.com/trends/explore?geo=%s&q=%s" % (geo, urllib.parse.quote(title))
            out.append({"title": title, "link": link, "meta": (traffic + " Suchanfragen") if traffic else ""})
    return out


def fetch_wikipedia(src, now):
    """Meistgelesene Wikipedia-Artikel des Vortags (Zugriffszahlen sind öffentlich)."""
    project = src["project"]                      # z. B. "de.wikipedia"
    base = src.get("api", "https://wikimedia.org/api/rest_v1/metrics/pageviews/top")
    last = None
    for back in (1, 2, 3):                        # die Daten kommen teils erst mit Verzögerung
        day = now - timedelta(days=back)
        url = "%s/%s/all-access/%04d/%02d/%02d" % (base, project, day.year, day.month, day.day)
        try:
            data = json.loads(fetch(url, headers={"User-Agent": WIKI_UA}))
            articles = data["items"][0]["articles"]
        except Exception as exc:
            last = exc
            continue
        out = []
        for a in articles:
            name = a.get("article", "")
            low = name.lower()
            if not name or ":" in name or low in WIKI_MAIN or any(b in low for b in WIKI_BLOCK):
                continue
            views = int(a.get("views", 0))
            out.append(
                {
                    "title": name.replace("_", " "),
                    "link": "https://%s.org/wiki/%s" % (project, urllib.parse.quote(name, safe="_()',!*~")),
                    "meta": "%s Aufrufe am %s" % (("{:,}".format(views)).replace(",", "."), day.strftime("%d.%m.")),
                }
            )
        return out
    raise last or ValueError("keine Daten")


def fetch_mastodon(src):
    inst = src.get("instance", "mastodon.social")
    url = src.get("url") or "https://%s/api/v1/trends/links?limit=%d" % (inst, TOP_N)
    out = []
    for link in json.loads(fetch(url))[:TOP_N]:
        hist = link.get("history") or [{}]
        people = sum(int(h.get("accounts", 0)) for h in hist[:2])
        parts = [clean(link.get("provider_name")), ("%d Personen teilen" % people) if people else ""]
        out.append(
            {
                "title": clean(link.get("title")) or link.get("url", ""),
                "link": safe_link(link.get("url")),
                "meta": " · ".join(x for x in parts if x),
            }
        )
    return out


def fetch_social(src, now):
    kind = src.get("type")
    if kind == "googletrends":
        return fetch_googletrends(src)
    if kind == "wikipedia":
        return fetch_wikipedia(src, now)
    if kind == "mastodon":
        return fetch_mastodon(src)
    raise ValueError("Unbekannter Typ: %r" % kind)


# ----------------------------------------------------------------- Übersetzung
class QuotaError(RuntimeError):
    pass


class Translator:
    """Übersetzt Überschriften ins Deutsche. Jede Überschrift wird nur einmal übersetzt
    (Zwischenspeicher in items.json). DeepL, wenn ein Schlüssel hinterlegt ist, sonst MyMemory."""

    def __init__(self, cache, now):
        self.cache = cache
        self.now = now
        self.deepl_key = os.environ.get("DEEPL_API_KEY", "").strip()
        self.deepl_url = os.environ.get("DEEPL_URL") or (
            "https://api-free.deepl.com/v2/translate" if self.deepl_key.endswith(":fx") else "https://api.deepl.com/v2/translate"
        )
        self.mm_url = os.environ.get("MYMEMORY_URL", "https://api.mymemory.translated.net/get")
        self.deepl_ok = bool(self.deepl_key)
        self.mm_ok = True
        self.notes = []
        self.new = Counter()    # neu übersetzt in diesem Lauf, je Dienst

    @staticmethod
    def _key(text, lang):
        return hashlib.sha1(("%s|%s" % (lang, text)).encode()).hexdigest()[:16]

    def get(self, text, lang):
        e = self.cache.get(self._key(text, lang))
        if e:
            e["seen"] = iso(self.now)
            return e["t"]
        return None

    def _put(self, text, lang, translated):
        self.cache[self._key(text, lang)] = {"t": translated, "seen": iso(self.now)}

    def prune(self, days=KEEP_DAYS):
        cutoff = self.now - timedelta(days=days)
        self.cache = {k: v for k, v in self.cache.items() if datetime.fromisoformat(v["seen"]) >= cutoff}

    def _deepl(self, texts, lang):
        body = json.dumps({"text": texts, "source_lang": lang.upper(), "target_lang": "DE"}).encode()
        raw = fetch(self.deepl_url, data=body, timeout=30,
                    headers={"Authorization": "DeepL-Auth-Key " + self.deepl_key, "Content-Type": "application/json"})
        result = [x["text"] for x in json.loads(raw)["translations"]]
        if len(result) != len(texts):
            raise ValueError("DeepL: unerwartete Antwort")
        return result

    def _mymemory(self, text, lang):
        url = self.mm_url + "?" + urllib.parse.urlencode({"q": text, "langpair": "%s|de" % lang})
        try:
            j = json.loads(fetch(url, timeout=20))
        except HttpFail as exc:
            if exc.code == 429:
                raise QuotaError("Tageslimit erreicht")
            raise
        out = html.unescape((j.get("responseData") or {}).get("translatedText") or "")
        if out.upper().startswith("MYMEMORY WARNING") or j.get("quotaFinished") or str(j.get("responseStatus")) == "429":
            raise QuotaError("Tageslimit erreicht")
        if str(j.get("responseStatus")) != "200" or not out:
            raise ValueError("Antwort unbrauchbar")
        return out

    def run(self, wanted):
        todo = sorted({(t, l) for t, l in wanted if self.get(t, l) is None})
        if len(todo) > MAX_NEW_TRANSLATIONS:
            self.notes.append("%d Überschriften folgen beim nächsten Lauf" % (len(todo) - MAX_NEW_TRANSLATIONS))
            todo = todo[:MAX_NEW_TRANSLATIONS]
        if self.deepl_ok and todo:
            by_lang = defaultdict(list)
            for t, l in todo:
                by_lang[l].append(t)
            for l, texts in by_lang.items():
                for i in range(0, len(texts), 40):
                    chunk = texts[i:i + 40]
                    try:
                        for t, translated in zip(chunk, self._deepl(chunk, l)):
                            self._put(t, l, translated)
                            self.new["DeepL"] += 1
                    except Exception as exc:
                        self.deepl_ok = False
                        self.notes.append("DeepL: " + describe(exc))
                        break
                if not self.deepl_ok:
                    break
        errors = 0
        for t, l in todo:
            if self.get(t, l) is not None:
                continue
            if not self.mm_ok or len(t.encode()) > 450:
                continue
            try:
                self._put(t, l, self._mymemory(t, l))
                self.new["MyMemory"] += 1
            except QuotaError as exc:
                self.mm_ok = False
                self.notes.append("MyMemory: " + str(exc))
            except Exception as exc:
                errors += 1
                if errors >= 3:
                    self.mm_ok = False
                    self.notes.append("MyMemory: " + describe(exc))
            time.sleep(PAUSE)


# ----------------------------------------------------------------- Hauptablauf
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sources", default="sources.json")
    ap.add_argument("--items", default="items.json")
    ap.add_argument("--out", default="data.json")
    args = ap.parse_args()

    now = now_utc()
    cfg = load_json(args.sources, None)
    if cfg is None:
        sys.exit("sources.json fehlt oder ist kein gültiges JSON (Komma oder Klammer vergessen?).")

    store = load_json(args.items, {})
    history = store.get("items", {})
    started = store.get("started") or iso(now)
    translator = Translator(store.get("translations", {}), now)

    feeds = {"news": cfg.get("news", [])}
    for region in REGIONS:
        feeds["pay_" + region] = cfg.get("payments", {}).get(region, [])

    status = []
    for cat, sources in feeds.items():
        for src in sources:
            row = {"source": src["name"], "category": cat, "ok": True, "count": 0, "error": ""}
            try:
                entries = load_entries(src)
                if not entries:
                    row["ok"] = False
                    row["error"] = "Feed enthält keine Meldungen"
                keywords = [k.lower() for k in src.get("keywords", [])]
                if keywords:  # nur Meldungen, deren Überschrift eines der Stichwörter enthält
                    entries = [e for e in entries if any(k in e["title"].lower() for k in keywords)]
                row["count"] = len(entries)
                update_history(history, cat, src["name"], entries, now)
            except Exception as exc:  # ein kaputter Feed darf nie alles stoppen
                row["ok"] = False
                row["error"] = describe(exc)
            status.append(row)

    # alte Einträge löschen
    cutoff = now - timedelta(days=KEEP_DAYS)
    history = {k: v for k, v in history.items() if effective_time(v) >= cutoff}

    def build(cat):
        sources = feeds[cat]
        names = {s["name"] for s in sources}
        weights = {s["name"]: s.get("weight", 1) for s in sources}
        order = {s["name"]: i for i, s in enumerate(sources)}
        langs = {s["name"]: s.get("lang", "de") for s in sources}
        items = []
        for v in history.values():
            if v["category"] == cat and v["source"] in names:
                items.append(
                    {"title": v["title"], "link": v["link"], "source": v["source"], "lang": langs.get(v["source"], "de"),
                     "time": effective_time(v), "tok": tokens(v["title"]), "image": v.get("image", "")}
                )
        return {w: top_stories(items, now, h, weights, order) for w, h in WINDOWS.items()}

    news = build("news")
    payments = {r: build("pay_" + r) for r in REGIONS}

    # Trends je Region
    cfg_social = cfg.get("social", {})
    if isinstance(cfg_social, list):   # alte Form: nur eine Liste
        cfg_social = {"de": cfg_social}
    social = {r: [] for r in REGIONS}
    for region in REGIONS:
        for src in cfg_social.get(region, []):
            row = {"source": src["name"], "category": "social_" + region, "ok": True, "count": 0, "error": ""}
            items = []
            try:
                items = fetch_social(src, now)[: src.get("limit", TOP_N)]
                row["count"] = len(items)
                if not items:
                    row["ok"] = False
                    row["error"] = "keine Einträge"
            except Exception as exc:
                row["ok"] = False
                row["error"] = describe(exc)
            status.append(row)
            lang = src.get("lang", "de")
            social[region].append(
                {"name": src["name"], "lang": lang if src.get("translate", True) else "de", "items": items}
            )

    # Übersetzen: alles, was angezeigt wird und nicht deutsch ist
    wanted = set()
    for lists in [news] + list(payments.values()):
        for stories in lists.values():
            for s in stories:
                if s["lang"] != "de":
                    wanted.add((s["title"], s["lang"]))
    for blocks in social.values():
        for b in blocks:
            if b["lang"] != "de":
                for it in b["items"]:
                    wanted.add((it["title"], b["lang"]))
    translator.run(wanted)

    def apply(entry, lang):
        if lang == "de":
            return
        translated = translator.get(entry["title"], lang)
        if translated and translated.strip().lower() != entry["title"].strip().lower():
            entry["title_orig"] = entry["title"]
            entry["title"] = translated

    for lists in [news] + list(payments.values()):
        for stories in lists.values():
            for s in stories:
                apply(s, s["lang"])
    for lists in [news] + list(payments.values()):
        for stories in lists.values():
            for s in stories:
                s.pop("lang", None)
    for blocks in social.values():
        for b in blocks:
            for it in b["items"]:
                apply(it, b["lang"])

    if wanted:
        missing = sum(1 for t, l in wanted if translator.get(t, l) is None)
        fresh = ", ".join("%s %d" % (k, v) for k, v in translator.new.items()) or "keine"
        info = "%d von %d Überschriften übersetzt (neu in diesem Lauf: %s)" % (len(wanted) - missing, len(wanted), fresh)
        if not translator.deepl_key:
            info += ". Ohne DeepL-Schlüssel wird der kostenlose Dienst MyMemory mit Tageslimit genutzt"
        if translator.notes:
            info += ". Hinweise: " + "; ".join(translator.notes)
        status.append(
            {
                "source": "Übersetzung", "category": "translate", "ok": missing == 0, "count": len(wanted) - missing,
                "info": info,
                "error": "%d Überschriften noch ohne Übersetzung. %s" % (missing, "; ".join(translator.notes)),
            }
        )
    translator.prune()

    result = {
        "generated": iso(now),
        "history_since": started,
        "news": news,
        "payments": payments,
        "social": social,
        "status": status,
    }

    Path(args.items).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.items).write_text(
        json.dumps({"started": started, "items": history, "translations": translator.cache}, ensure_ascii=False, indent=0),
        encoding="utf-8",
    )
    Path(args.out).write_text(json.dumps(result, ensure_ascii=False, indent=1), encoding="utf-8")

    ok = sum(1 for s in status if s["ok"])
    print("Fertig: %d von %d Quellen erreichbar, %d Meldungen in der Historie." % (ok, len(status), len(history)))
    for s in status:
        if not s["ok"]:
            print("  Problem bei %s (%s): %s" % (s["source"], s["category"], s["error"]))


if __name__ == "__main__":
    main()
