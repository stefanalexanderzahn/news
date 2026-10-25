#!/usr/bin/env python3
"""News-Dashboard: holt die Feeds aus sources.json, sammelt eine Historie
und bildet quellenübergreifende Top-10-Listen für 24 Stunden, 7 Tage und 30 Tage.

Nur Python-Standardbibliothek, keine Installation nötig.
"""
import argparse
import email.utils
import hashlib
import html
import json
import re
import sys
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path

UA = "Mozilla/5.0 (compatible; NewsDashboard/1.0)"
WINDOWS = {"24h": 24, "7d": 24 * 7, "30d": 24 * 30}
KEEP_DAYS = 35
TOP_N = 10
SIM_THRESHOLD = 0.5

STOP = set(
    """der die das den dem des ein eine einer einem einen eines und oder aber mit von für auf aus bei
    nach über unter vor zum zur im in am an ist sind war waren wird werden wurde wurden hat haben hatte
    nicht auch noch nur wie als dass sich sein ihre ihr ihren kann können soll sollen will wollen muss
    müssen mehr neue neuer neues gegen ohne sagt warum wer was wann wo wegen durch bis seit zwischen
    jetzt heute gibt geben geht gehen the and for with from that this are was were has have not you
    your new says will its into over after about""".split()
)

CATEGORIES = ["news", "pay_de", "pay_eu", "pay_world"]


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


def fetch(url, timeout=25):
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "*/*"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


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


def parse_feed(data):
    """RSS 2.0 und Atom -> Liste aus {title, link, date}."""
    root = ET.fromstring(data)
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
        if d.get("title"):
            out.append(
                {
                    "title": d["title"],
                    "link": safe_link(d.get("link")),
                    "date": parse_date(d.get("date")),
                }
            )
    return out


# ----------------------------------------------------------------- Nachrichten / Payments
def update_history(history, category, source, entries, now):
    added = 0
    for e in entries:
        key = hashlib.sha1((category + "|" + (e["link"] or e["title"])).encode()).hexdigest()[:16]
        if key in history:
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
        stories.append(
            {
                "score": score,
                "title": lead["title"],
                "link": lead["link"],
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


# ----------------------------------------------------------------- Social
def fetch_social(src):
    kind = src.get("type")
    if kind == "googletrends":
        root = ET.fromstring(fetch(src["url"]))
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
                    link = "https://trends.google.de/trends/explore?geo=DE&q=" + urllib.parse.quote(title)
                out.append({"title": title, "link": link, "meta": (traffic + " Suchanfragen") if traffic else ""})
        return out[:TOP_N]
    if kind == "reddit":
        url = src.get("url") or "https://www.reddit.com/r/%s/top.json?t=day&limit=%d" % (src["subreddit"], TOP_N)
        data = json.loads(fetch(url))
        out = []
        for ch in data["data"]["children"][:TOP_N]:
            d = ch["data"]
            out.append(
                {
                    "title": clean(d.get("title")),
                    "link": "https://www.reddit.com" + d.get("permalink", ""),
                    "meta": "%s Punkte · %s Kommentare" % (d.get("score", 0), d.get("num_comments", 0)),
                }
            )
        return out
    if kind == "rss":
        return [
            {"title": e["title"], "link": e["link"], "meta": ""} for e in parse_feed(fetch(src["url"]))[:TOP_N]
        ]
    raise ValueError("Unbekannter Social-Typ: %r" % kind)


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

    feeds = {"news": cfg.get("news", [])}
    for region in ("de", "eu", "world"):
        feeds["pay_" + region] = cfg.get("payments", {}).get(region, [])

    status = []
    for cat, sources in feeds.items():
        for src in sources:
            row = {"source": src["name"], "category": cat, "ok": True, "count": 0, "error": ""}
            try:
                entries = parse_feed(fetch(src["url"]))
                row["count"] = len(entries)
                if not entries:
                    row["ok"] = False
                    row["error"] = "Feed enthält keine Meldungen"
                update_history(history, cat, src["name"], entries, now)
            except Exception as exc:  # ein kaputter Feed darf nie alles stoppen
                row["ok"] = False
                row["error"] = "%s: %s" % (type(exc).__name__, str(exc)[:120])
            status.append(row)

    # alte Einträge löschen
    cutoff = now - timedelta(days=KEEP_DAYS)
    history = {k: v for k, v in history.items() if effective_time(v) >= cutoff}

    # Auswertung
    def build(cat):
        sources = feeds[cat]
        names = {s["name"] for s in sources}
        weights = {s["name"]: s.get("weight", 1) for s in sources}
        order = {s["name"]: i for i, s in enumerate(sources)}
        items = []
        for v in history.values():
            if v["category"] == cat and v["source"] in names:
                items.append(
                    {"title": v["title"], "link": v["link"], "source": v["source"],
                     "time": effective_time(v), "tok": tokens(v["title"])}
                )
        return {w: top_stories(items, now, h, weights, order) for w, h in WINDOWS.items()}

    social = []
    for src in cfg.get("social", []):
        row = {"source": src["name"], "category": "social", "ok": True, "count": 0, "error": ""}
        items = []
        try:
            items = fetch_social(src)
            row["count"] = len(items)
            if not items:
                row["ok"] = False
                row["error"] = "keine Einträge"
        except Exception as exc:
            row["ok"] = False
            row["error"] = "%s: %s" % (type(exc).__name__, str(exc)[:120])
        status.append(row)
        social.append({"name": src["name"], "items": items})

    result = {
        "generated": iso(now),
        "history_since": started,
        "news": build("news"),
        "payments": {"de": build("pay_de"), "eu": build("pay_eu"), "world": build("pay_world")},
        "social": social,
        "status": status,
    }

    Path(args.items).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.items).write_text(
        json.dumps({"started": started, "items": history}, ensure_ascii=False, indent=0), encoding="utf-8"
    )
    Path(args.out).write_text(json.dumps(result, ensure_ascii=False, indent=1), encoding="utf-8")

    ok = sum(1 for s in status if s["ok"])
    print("Fertig: %d von %d Quellen erreichbar, %d Meldungen in der Historie." % (ok, len(status), len(history)))
    for s in status:
        if not s["ok"]:
            print("  Problem bei %s (%s): %s" % (s["source"], s["category"], s["error"]))


if __name__ == "__main__":
    main()
