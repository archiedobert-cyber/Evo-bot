"""Posts evolutions labelled "New" on fut.gg/evolutions to a Discord channel via webhook.

An evo is posted when it shows the "New" label now but did not show it at the
previous run. So an evo that keeps its label for several days is posted once,
and one that comes back with the label again is posted again. posted.json only
remembers which evos were labelled New last time.

Env vars (same names as the other bots, so the same workflow file works):
  DISCORD_WEBHOOK_URL  webhook to post to (GitHub secret)
  PING_ROLE_ID         optional role ID to ping after the post (GitHub secret)
  DRY_RUN=1            print what would be posted instead of sending it
  TEST_MODE=1          post the evos currently labelled New (or the first few on the page if none), even if already posted
  TEST_URL=<link>      post just this one evo page, skipping the site scan
"""
import json
import os
import re
import sys
import time
from datetime import datetime, timezone
from itertools import islice
from pathlib import Path
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup, Comment, NavigableString, Tag

BASE = "https://www.fut.gg"
LIST_URL = f"{BASE}/evolutions/"
STATE_FILE = Path("posted.json")  # remembers what's already been posted
WEBHOOK = os.environ.get("DISCORD_WEBHOOK_URL")
DRY_RUN = os.environ.get("DRY_RUN") == "1"
TEST_MODE = os.environ.get("TEST_MODE") == "1"
TEST_URL = os.environ.get("TEST_URL", "").strip()

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
    )
}

# Links to individual evos, e.g. /evolutions/2525-flank-identity/
# (the numeric id stops pages like /evolutions/expired/ or
# /evolutions/2525-flank-identity/eligible-players/ matching)
EVO_HREF = re.compile(r"^(?:https://www\.fut\.gg)?/evolutions/\d+-[^/]+/?$")
# The "New" label must be exactly "New". It can be its own text piece ("New")
# or stuck onto the end of the title ("Trust the KeeperNew").
NEW_BADGE = re.compile(r"^\s*new\s*$", re.I)
NEW_SUFFIX = re.compile(r"[a-z0-9)!?.]New$")

# How long to keep re-checking the site for new content (scheduled runs set
# POLL_MINUTES; 0 = check once), and how many seconds between checks.
POLL_MINUTES = float(os.environ.get("POLL_MINUTES") or 0)
POLL_EVERY = 20

# In test mode, how many evos from the top of the page to post
TEST_LIMIT = 3

# Title line shown above the evo cards - edit the text/emojis however you like
HEADER = "# 🚨 🆕 **NEW EVO** 🆕 🚨"

# Message posted at the very bottom, after all the cards. "" = no footer.
FOOTER = ""

# Role to ping after the post. Set as a GitHub secret named PING_ROLE_ID
# (numbers only) or paste the ID here. "" = no ping.
PING_ROLE_ID = os.environ.get("PING_ROLE_ID", "").strip()

# Emoji shown in front of each upgrade (not the OVR one, which always gets ⭐️).
# "" = none. Example: "🔹"
UPGRADE_ICON = ""

# How many upgrades per line
UPGRADES_PER_LINE = 5

# Where to put the evo's picture: "thumbnail" (small, top right), "image" (big,
# at the bottom) or "" (no picture). The bot looks for a picture on the evo page,
# then on its card on the listing page.
IMAGE_MODE = "thumbnail"

SKIP = ["script", "style", "nav", "header", "footer"]


def get(url):
    r = requests.get(url, headers=HEADERS, timeout=30)
    r.raise_for_status()
    return r.text


IMAGE_ATTRS = ("src", "data-src", "data-original", "data-lazy-src", "data-lazy", "data-image", "data-url")
BAD_IMAGE = ("fut-social", "favicon", "logo", "placeholder", "default-image", "public-assets", "sp.webp")


def img_source(img):
    """Best image URL an <img> tag carries (src, lazy-load attrs, srcset)."""
    candidates = [img.get(a) for a in IMAGE_ATTRS]
    srcset = img.get("srcset") or img.get("data-srcset")
    if srcset:
        for item in srcset.split(","):
            parts = item.strip().split()
            if parts:
                candidates.append(parts[0])
    for src in candidates:
        if not src or src.startswith("data:"):
            continue
        src = urljoin(BASE, src.strip())
        if any(b in src.lower() for b in BAD_IMAGE):
            continue
        return src
    return None


def bigger(src):
    """fut.gg serves resized images (.../width=300/...); ask for a larger one."""
    return re.sub(r"width=\d+", "width=600", src) if src else src


def img_candidates(root):
    """Every usable picture inside root, in page order (nav/header/footer skipped)."""
    out = []
    for img in root.find_all("img"):
        if img.find_parent(SKIP):
            continue
        src = bigger(img_source(img))
        if src and src not in out:
            out.append(src)
    return out


def clean_text(s):
    return re.sub(r"\s+", " ", str(s)).strip()


def page_text(page):
    """Raw page HTML with escaped JSON quotes un-escaped, for regex searching."""
    return str(page).replace('\\"', '"')


# --------------------------------------------------------------------------
# Reading the evo page
# --------------------------------------------------------------------------

def page_sections(page):
    """Split the evo page into {heading: [text pieces]} using its <h2> headings.
    Only the first block with a given heading is kept (the page repeats some
    blocks further down). Also returns every text piece on the page, in order,
    as a fallback."""
    root = page.find("main") or page.body or page
    sections, current, everything = {}, None, []
    for el in root.descendants:
        if isinstance(el, Tag):
            if el.name in ("h1", "h2") and not el.find_parent(SKIP):
                name = clean_text(el.get_text(" ", strip=True)).lower()
                if el.name == "h1" or name in sections:
                    current = None
                else:
                    current = sections.setdefault(name, [])
            continue
        if not isinstance(el, NavigableString) or isinstance(el, Comment):
            continue
        if el.find_parent(SKIP + ["h1", "h2"]):
            continue
        text = clean_text(el)
        if not text:
            continue
        if text.startswith("©"):
            break
        everything.append(text)
        if current is not None:
            current.append(text)
    return sections, everything


# Labels that can appear on the page; used to tell "value missing" from "value"
LABELS = {
    "type", "submit by", "expiry", "expires", "coins cost", "points cost",
    "overall", "position", "excluded position", "excluded positions",
    "max ps", "pace", "max pos.", "games", "wins", "clean sheets", "online required",
}


def value_after(tokens, label_re):
    """The text piece right after a label ('' if the label or its value is missing)."""
    for i, t in enumerate(tokens):
        if re.fullmatch(label_re, t, re.I):
            nxt = tokens[i + 1] if i + 1 < len(tokens) else ""
            return "" if nxt.lower() in LABELS else nxt
    return ""


POS_TOKEN = re.compile(r"^[A-Z]{2,3}(?:\s*,\s*[A-Z]{2,3})*\s*,?$")


def positions_after(tokens, label_re):
    """Position codes after a label, whether the page gives them as 'LM, LW'
    or as separate pieces ('LM', 'LW')."""
    for i, t in enumerate(tokens):
        if re.fullmatch(label_re, t, re.I):
            out = []
            for u in tokens[i + 1 :]:
                if u == ",":
                    continue
                if POS_TOKEN.match(u):
                    out.extend(p.strip() for p in u.split(",") if p.strip())
                else:
                    break
            return list(dict.fromkeys(out))
    return []


def tidy_max(v):
    """'Max. 79' -> 'Max 79'"""
    return re.sub(r"\b(Max|Min)\.", r"\1", v).strip()


ATTR_NAMES = {"WF": "Weak Foot", "SM": "Skill Moves", "Fk Accuracy": "FK Accuracy"}
UPG_FULL = re.compile(r"^\+\s*(\d+)\s+([A-Za-z][A-Za-z .'/-]*?)\s*(\d+)$")  # "+5 OVR80" / "+5 OVR 80"
UPG_NAME = re.compile(r"^\+\s*(\d+)\s+([A-Za-z][A-Za-z .'/-]*?)$")  # "+5 OVR"
AMOUNT_ONLY = re.compile(r"^\+\s*(\d+)$")  # "+5"
NAME_ONLY = re.compile(r"^([A-Za-z][A-Za-z .'/-]*?)\s*(\d+)?$")  # "OVR" or "OVR80"
MAX_ONLY = re.compile(r"^(?:max\.?\s*)?(\d+)$", re.I)  # "80"
POSITION_PREFIX = re.compile(r"^(?:GK|CB|RB|LB|RWB|LWB|CDM|CM|CAM|RM|LM|RW|LW|CF|ST)(?=[A-Z][a-z])")
NOT_PLAYSTYLE = re.compile(r"^(?:\d+|[A-Z]|option\s+\w|recommended|pick one|[A-Z]{2,3})$", re.I)


def parse_upgrades(tokens):
    """-> (upgrades [{'amount','name','max'}], playstyles [str]).
    Copes with the page giving an upgrade as one piece ("+5 OVR80"), as two
    ("+5 OVR", "80") or as three ("+5", "OVR", "80")."""
    ups, styles, i, n = [], [], 0, len(tokens)
    while i < n:
        t = tokens[i]
        amount = name = mx = None
        step = 1
        m = UPG_FULL.match(t)
        if m:
            amount, name, mx = m.groups()
        else:
            m = UPG_NAME.match(t)
            if m:
                amount, name = m.groups()
                nxt = MAX_ONLY.match(tokens[i + 1]) if i + 1 < n else None
                if nxt:
                    mx, step = nxt.group(1), 2
            else:
                m = AMOUNT_ONLY.match(t)
                nm = NAME_ONLY.match(tokens[i + 1]) if m and i + 1 < n else None
                if m and nm:
                    amount, name, mx = m.group(1), nm.group(1), nm.group(2)
                    step = 2
                    if mx is None and i + 2 < n and MAX_ONLY.match(tokens[i + 2]):
                        mx, step = MAX_ONLY.match(tokens[i + 2]).group(1), 3
        if amount is None:
            if not NOT_PLAYSTYLE.match(t) and not t.startswith("+"):
                styles.append(POSITION_PREFIX.sub("", t))
            i += 1
            continue
        i += step
        name = name.strip()
        ups.append({"amount": amount, "name": ATTR_NAMES.get(name, name), "max": mx})
    # same upgrade twice (e.g. repeated blocks) -> keep the first
    seen, unique = set(), []
    for u in ups:
        if u["name"] not in seen:
            seen.add(u["name"])
            unique.append(u)
    return unique, list(dict.fromkeys(styles))


def online_required(page):
    """True/False for the 'Online Required' tick or cross. The value is an icon,
    so look at what sits in the same box as the label."""
    for node in page.find_all(string=re.compile(r"^\s*Online Required\s*$", re.I)):
        if node.find_parent(["script", "style"]):
            continue
        box = node.parent.parent if node.parent is not None and node.parent.parent is not None else node.parent
        html = str(box).lower().replace(str(node).lower(), "")
        print(f"DEBUG online-required cell: {html[:300]!r}")
        yes = re.search(r"check|tick|✓|✔|\byes\b|\btrue\b", html)
        no = re.search(r"x-?mark|cross|close|✗|✘|✕|\bno\b|\bfalse\b|lucide-x\b|circle-x|x-circle", html)
        return bool(yes and not no)
    return False


# --------------------------------------------------------------------------
# Submit by / Expiry
# --------------------------------------------------------------------------

def parse_when(value):
    """datetime from an ISO string or epoch number, else None."""
    v = str(value).strip()
    if re.fullmatch(r"\d{10,13}", v):
        ts = int(v)
        ts = ts / 1000 if ts > 10**11 else ts
        return datetime.fromtimestamp(ts, timezone.utc)
    try:
        dt = datetime.fromisoformat(v.replace("Z", "+00:00"))
    except ValueError:
        return None
    return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)


def in_text(seconds):
    if seconds <= 0:
        return "expired"
    days, rem = divmod(int(seconds), 86400)
    hours = rem // 3600
    if days:
        return f"in {days} day{'s' if days != 1 else ''}"
    if hours:
        return f"in {hours} hour{'s' if hours != 1 else ''}"
    return "in under an hour"


def relative(value):
    """Turn whatever the page gives (a date, '9 days', 'in 9 days') into 'in 9 days'."""
    v = clean_text(value)
    if not v:
        return ""
    dt = parse_when(v)
    if dt:
        return in_text((dt - datetime.now(timezone.utc)).total_seconds())
    if "ago" in v.lower():
        return v
    m = re.search(r"(\d+)\s*(days?|hours?|hrs?|minutes?|mins?|weeks?|months?)", v, re.I)
    if m:
        return f"in {m.group(1)} {m.group(2).lower()}"
    m = re.match(r"^(\d+)\s*d\b", v, re.I)
    if m:
        return f"in {m.group(1)} days"
    return v


SUBMIT_KEYS = r"submitBy\w*|submitDeadline|submissionDeadline|submit_by\w*|lastSubmit\w*"
EXPIRY_KEYS = r"expiresAt|expiryDate|expirationDate|expiry|expireAt|endsAt|endDate|endTime|expires"


def json_deadline(html, keys):
    m = re.search(
        r'"?(?:' + keys + r')"?\s*:\s*"?(\d{4}-\d{2}-\d{2}T[^",}\s]+|\d{10,13})',
        html,
        re.I,
    )
    return m.group(1) if m else ""


def dom_deadline(page, label):
    """Value shown next to a 'Submit by' / 'Expiry' label (a <time datetime=...>
    tag or plain text)."""
    pat = re.compile(rf"^\s*{label}\s*$", re.I)
    for node in page.find_all(string=pat):
        if node.find_parent(["script", "style"]):
            continue
        for el in islice(node.next_elements, 25):
            if isinstance(el, Tag):
                if el.name == "time" and el.get("datetime"):
                    return el["datetime"]
                continue
            if isinstance(el, Comment) or el.find_parent(["script", "style"]):
                continue
            text = clean_text(el)
            if not text:
                continue
            if text.lower() in LABELS:
                return ""  # ran into the next label, so this one has no value
            return text
    return ""


def find_deadline(page, html, label, keys):
    raw = json_deadline(html, keys) or dom_deadline(page, label)
    return relative(raw)


# --------------------------------------------------------------------------
# Building the post
# --------------------------------------------------------------------------

def find_title(page, url):
    tag = page.find("h1") or page.find("title")
    title = tag.get_text(" ", strip=True) if tag else url.rstrip("/").split("/")[-1]
    return re.sub(r"\s*-\s*EA SPORTS FC.*$", "", title).strip()


def number(v):
    """The value if it is a plain number, else ''."""
    return v if re.fullmatch(r"\d+", v or "") else ""


def training_time(tokens):
    """'1 day', '3 hours' ... for Training Camp evos, else ''."""
    m = re.search(
        r"training time\s*:?\s*(\d+)\s*(weeks?|days?|hours?|hrs?|minutes?|mins?)",
        " ".join(tokens),
        re.I,
    )
    if not m:
        return ""
    n, unit = int(m.group(1)), m.group(2).lower()
    unit = {"hr": "hour", "hrs": "hour", "min": "minute", "mins": "minute"}.get(unit, unit.rstrip("s"))
    return f"{n} {unit}{'' if n == 1 else 's'}"


def build_evo(url, page):
    sections, everything = page_sections(page)
    print(f"DEBUG sections found: {list(sections)}")
    html = page_text(page)

    reqs = sections.get("player requirements") or everything
    details = sections.get("details") or everything
    upgrades = sections.get("evolution upgrades") or everything
    challenges = sections.get("challenges") or everything

    ups, styles = parse_upgrades(upgrades)

    evo = {
        "url": url,
        "title": find_title(page, url),
        "coins": value_after(details, r"coins cost"),
        "points": value_after(details, r"points cost"),
        "overall": tidy_max(value_after(reqs, r"overall")),
        "positions": positions_after(reqs, r"position"),
        "excluded": positions_after(reqs, r"excluded positions?"),
        "upgrades": ups,
        "playstyles": styles,
        "training": training_time(everything),
        "games": number(value_after(challenges, r"games")),
        "wins": number(value_after(challenges, r"wins")),
        "clean_sheets": number(value_after(challenges, r"clean sheets")),
        "online": online_required(page),
        "submit": find_deadline(page, html, "Submit by", SUBMIT_KEYS),
        "expiry": find_deadline(page, html, "Expiry", EXPIRY_KEYS),
    }

    print(f"DEBUG upgrade pieces: {upgrades[:40]}")
    images = img_candidates(page.find("main") or page.body or page)
    print(f"DEBUG images on evo page: {images[:8]}")
    evo["image"] = images[0] if images else None

    if not evo["submit"] and not evo["expiry"]:
        # Nothing found - print what the page does say so it can be fixed
        hints = re.findall(r".{0,40}(?:submit|expir|deadline).{0,60}", html, re.I)[:6]
        print("DEBUG no submit/expiry found; nearby text:", hints)
    return evo


def upgrade_text(u, icon=""):
    label = f"{icon} +{u['amount']} {u['name']}".strip()
    return f"**{label}** - Max {u['max']}" if u["max"] else f"**{label}**"


def to_embed(evo):
    parts = [f"## 🆕 {evo['title']}\n[More Info]({evo['url']})"]

    reqs = []
    if evo["overall"]:
        reqs.append(f"**Overall** - {evo['overall']}")
    if evo["positions"]:
        reqs.append(f"**Position** - {', '.join(evo['positions'])}")
    if evo["excluded"]:
        reqs.append(f"**Excluded Positions** - {', '.join(evo['excluded'])}")
    if reqs:
        parts.append("## ☑️ Requirements\n" + "\n".join(reqs))

    ups = evo["upgrades"]
    if ups or evo["playstyles"]:
        lines = []
        ovr = [u for u in ups if u["name"].upper() == "OVR"]
        rest = [u for u in ups if u["name"].upper() != "OVR"]
        for u in ovr:
            lines.append(upgrade_text({**u, "name": "OVR"}, "⭐️"))
        for i in range(0, len(rest), UPGRADES_PER_LINE):
            lines.append(", ".join(upgrade_text(u, UPGRADE_ICON) for u in rest[i : i + UPGRADES_PER_LINE]))
        block = "## ⬆️ Upgrades\n" + "\n".join(lines)
        if evo["playstyles"]:
            block += "\n\n**Playstyles**\n" + ", ".join(evo["playstyles"])
        parts.append(block)

    # Challenges depend on the kind of evo:
    #  - Training Camp: shows how long it takes instead of games
    #  - standard: games / wins / clean sheets / online
    #  - cosmetic (nothing to play or wait for): no Challenges section at all
    chal = []
    if evo["training"]:
        chal.append(f"**Training Time** - {evo['training']}")
    elif any(v not in ("", "0") for v in (evo["games"], evo["wins"], evo["clean_sheets"])):
        chal.append(f"**Games** - {evo['games'] or 0}")
        chal.append(f"**Wins** - {evo['wins'] or 0}")
        chal.append(f"**Clean Sheets** - {evo['clean_sheets'] or 0}")
        chal.append(f"**Online Required** - {'✅' if evo['online'] else '❌'}")
    if chal:
        parts.append("## 📋 Challenges\n" + "\n".join(chal))

    cost = []
    if evo["coins"]:
        cost.append(f"**Coins** - {evo['coins']}")
    if evo["points"]:
        cost.append(f"**Points** - {evo['points']}")
    if cost:
        parts.append("## 💰 Cost\n" + "\n".join(cost))

    avail = []
    if evo["submit"]:
        avail.append(f"**Submit by** - {evo['submit']}")
    if evo["expiry"]:
        avail.append(f"**Expiry** - {evo['expiry']}")
    if avail:
        parts.append("## ⏰ Available For\n" + "\n".join(avail))

    embed = {"description": "\n\n".join(parts)[:4000], "color": 0x3498DB}

    if evo.get("image") and IMAGE_MODE in ("thumbnail", "image"):
        embed[IMAGE_MODE] = {"url": evo["image"]}

    print("DEBUG EMBED:")
    print(json.dumps(embed, indent=2, ensure_ascii=False))
    return embed


# --------------------------------------------------------------------------
# Finding "New" evos on the listing page
# --------------------------------------------------------------------------

def card_container(anchor):
    """Walk up from a link until the parent holds more than one evo (= the card)."""
    node = anchor
    while node.parent is not None and node.parent.name not in ("body", "html"):
        hrefs = {a["href"] for a in node.parent.find_all("a", href=EVO_HREF)}
        if len(hrefs) > 1:
            break
        node = node.parent
    return node


def card_info(anchor):
    """Is the whole card labelled New (the badge can sit outside the link)?"""
    card = card_container(anchor)
    is_new = any(
        NEW_BADGE.match(str(t))
        for t in card.find_all(string=True)
        if not t.find_parent(["script", "style"])
    ) or any(NEW_SUFFIX.search(a.get_text("", strip=True)) for a in card.find_all("a"))
    return {"new": is_new, "text": card.get_text(" ", strip=True), "images": img_candidates(card)}


def find_evo_links(html):
    """Every evo on the listing page, in page order, as {url: {"new": bool}}."""
    soup = BeautifulSoup(html, "html.parser")
    found = {}
    for a in soup.find_all("a", href=EVO_HREF):
        url = urljoin(BASE, a["href"])
        info = card_info(a)
        old = found.get(url)
        if old:
            info["new"] = info["new"] or old["new"]
            info["images"] = old["images"] + [i for i in info["images"] if i not in old["images"]]
        found[url] = info
    if not found:
        sys.exit("No evo cards found - the page layout may have changed.")
    new_count = sum(i["new"] for i in found.values())
    print(f"Found {len(found)} evos on the page, {new_count} labelled New")
    for url, i in list(found.items())[:3]:
        print(f"DEBUG card {url}: new={i['new']} text={i['text'][:150]!r} images={i['images'][:3]}")
    return found


def load_state():
    """URLs that were labelled New at the previous run, or None on a first run."""
    if not STATE_FILE.exists():
        return None
    try:
        data = json.loads(STATE_FILE.read_text())
    except ValueError:
        return None
    if isinstance(data, dict) and isinstance(data.get("new"), list):
        return set(data["new"])
    return None


def save_state(new_urls):
    STATE_FILE.write_text(json.dumps({"new": sorted(new_urls)}, indent=2))


def load_evo(url, card_images=()):
    try:
        page = BeautifulSoup(get(url), "html.parser")
    except requests.RequestException as e:
        print(f"Could not fetch evo page {url}: {e}")
        return None
    evo = build_evo(url, page)
    if not evo["image"] and card_images:
        evo["image"] = card_images[0]  # fall back to the picture on the listing card
    return evo


def post(embeds):
    for i in range(0, len(embeds), 10):  # Discord allows 10 embeds per message
        payload = {"embeds": embeds[i : i + 10]}
        if i == 0:
            payload["content"] = HEADER
        r = requests.post(WEBHOOK, json=payload, timeout=30)
        r.raise_for_status()
        time.sleep(1)

    if FOOTER or PING_ROLE_ID:
        content = f"<@&{PING_ROLE_ID}> {FOOTER}".strip() if PING_ROLE_ID else FOOTER
        # flags=4 stops Discord adding a big link preview under the footer
        payload = {"content": content, "flags": 4}
        if PING_ROLE_ID:  # only this role can be pinged, nothing else
            payload["allowed_mentions"] = {"roles": [PING_ROLE_ID]}
        r = requests.post(WEBHOOK, json=payload, timeout=30)
        r.raise_for_status()


def main():
    if not WEBHOOK and not DRY_RUN:
        sys.exit("DISCORD_WEBHOOK_URL is not set")

    if TEST_URL:
        print(f"TEST_URL set - posting just this one evo: {TEST_URL}")
        page = BeautifulSoup(get(TEST_URL), "html.parser")
        embed = to_embed(build_evo(TEST_URL, page))
        if DRY_RUN:
            print(json.dumps([embed], indent=2, ensure_ascii=False))
        else:
            post([embed])
        return

    if TEST_MODE:
        found = find_evo_links(get(LIST_URL))
        # Prefer evos labelled New; if none are, use the first few on the page
        new_urls = [u for u, i in found.items() if i["new"]][:TEST_LIMIT] or list(found)[:TEST_LIMIT]
        print(f"Test mode - posting {len(new_urls)} evo(s), ignoring what was posted before")
        new = [e for e in (load_evo(u, found[u]["images"]) for u in new_urls) if e]
        embeds = [to_embed(e) for e in new]
        if DRY_RUN:
            print(json.dumps(embeds, indent=2, ensure_ascii=False))
        elif embeds:
            post(embeds)
        return

    previous = load_state()
    if previous is None:
        print("First run - posting everything currently labelled New")
        previous = set()

    # New content only appears on the site at release time, so keep checking
    # for up to POLL_MINUTES and post the moment something new turns up.
    deadline = time.time() + POLL_MINUTES * 60
    while True:
        found = find_evo_links(get(LIST_URL))
        labelled = {u for u, i in found.items() if i["new"]}
        new_urls = [u for u in found if u in labelled and u not in previous]
        print(f"{len(new_urls)} evo(s) to post")

        new = [e for e in (load_evo(u, found[u]["images"]) for u in new_urls) if e]
        if new or time.time() >= deadline:
            break
        print(f"Nothing new yet - checking again in {POLL_EVERY}s")
        time.sleep(POLL_EVERY)

    if new:
        embeds = [to_embed(e) for e in new]
        if DRY_RUN:
            print(json.dumps(embeds, indent=2, ensure_ascii=False))
        else:
            post(embeds)

    if not DRY_RUN:
        save_state(labelled)  # only reached if posting didn't fail


if __name__ == "__main__":
    main()
