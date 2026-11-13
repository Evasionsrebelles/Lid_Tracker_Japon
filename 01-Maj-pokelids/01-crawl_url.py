#!/usr/bin/env python3
"""
01-crawl_url.py (v11) — Pipeline fusionné 01+02+03+04 avec vérification à deux niveaux.

Un seul script, un seul dossier d'images. Produit :
  • pokelid.kml        carte Google Earth / My Maps (kanji intégré)
  • pokelid.json       mêmes données que le KML (carte web, kanji intégré)
  • images_webp/       icônes locales (fallback)
  • .cache/            fichiers internes (invisibles, supprimables)

--- Comportement d'un nouveau lancement (v11) ---
Un nouveau lancement CHERCHE les nouveautés et les modifications :

  1. RESOLVE : revisite SYSTÉMATIQUEMENT les 47 pages de préfecture.
  2. SCRAPE : classification (new, modified, same) :
       • new       → scrape complet (image_url = repo GitHub, image commitée dans ce run)
       • modified  → re-scrape ciblé (image_url = repo GitHub, image commitée dans ce run)
       • same      → inchangée → image_url réécrite vers le repo GitHub !
  3. KANJI : résolution des kanji villes.
  4. GENERATE : écrit pokelid.kml + pokelid.json avec les bonnes URLs.

--- URLs GitHub ---
Toutes les plaques (new/modified/same) pointent vers :
https://raw.githubusercontent.com/Evasionsrebelles/Lid_Tracker_Japon/main/01-Maj-pokelids/images_webp/icon-ci-{id}.webp
(l'image est toujours téléchargée/encodée localement AVANT génération du JSON/KML, puis
commitée dans le même run par l'étape "git add -A" du workflow — le lien est donc valide
dès que le job se termine.)

Usage :
    pip install requests beautifulsoup4 pillow tqdm
    python 01-crawl_url.py
    python 01-crawl_url.py --deep-check
    python 01-crawl_url.py --force
    python 01-crawl_url.py --resume-only
    python 01-crawl_url.py --limit 20
"""

import argparse
import csv
import difflib
import hashlib
import io
import json
import re
import sys
import threading
import time
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from html import unescape
from pathlib import Path
from urllib.parse import urljoin
from xml.sax.saxutils import escape

import requests
from bs4 import BeautifulSoup
from PIL import Image

try:
    from tqdm import tqdm
except ImportError:
    tqdm = None

# ══════════════════════════════════════════════════════════════════════════
# Configuration
# ══════════════════════════════════════════════════════════════════════════

BASE_DIR   = Path(__file__).resolve().parent
CACHE_DIR  = BASE_DIR / ".cache"

# Livrables
KML_FILE   = BASE_DIR / "pokelid.kml"
JSON_FILE  = BASE_DIR / "pokelid.json"
IMAGES_DIR = BASE_DIR / "images_webp"

# Caches
REGIONS_CACHE = CACHE_DIR / "regions_cache.json"
RESUME_CACHE  = CACHE_DIR / "resume_data.json"
KANJI_CACHE   = CACHE_DIR / "kanji_cache.json"
KANJI_MISSING = CACHE_DIR / "villes_non_trouvees.csv"

# Optionnels
REGIONS_TMP    = BASE_DIR / "regions.json"
GEONAMES       = BASE_DIR / "JP.txt"
POKEMON_NAMES  = BASE_DIR / "pokemon_names.json"
POKEMON_LEGACY = BASE_DIR / "pokemon_fr_en.json"

# ── URLs GitHub ────────────────────────────────────────────────────────────
GITHUB_RAW_BASE = "https://raw.githubusercontent.com/Evasionsrebelles/Lid_Tracker_Japon/main/01-Maj-pokelids/images_webp"

DEFAULT_HEADERS = {"User-Agent": "Mozilla/5.0 (compatible; PokeLidsPipeline/11.0)"}

MANHOLE_DESC_RE = re.compile(r"/manhole/desc/(\d+)/?")
BASE_PREFECTURE = "https://local.pokemon.jp/en/manhole/{slug}.html"
PROBE_URL       = "https://local.pokemon.jp/en/manhole/desc/{id}/?is_modal=1"

ICON_SIZE       = (256, 256)
DEFAULT_WORKERS = 8
HEAD_TIMEOUT    = 10

WEBP_QUALITY  = 80
WEBP_LOSSLESS = False
WEBP_METHOD   = 6

KANJI_SAVE_INTERVAL = 5
WIKI_DELAY   = 1.0
WIKI_TIMEOUT = 15
ADMIN_SUFFIXES = ["-shi", "-chou", "-cho", "-mura", "-gun", "-ku"]
MANUAL_CITIES = {
    "Aizubange": "会津坂下町", "Iitate": "飯舘村", "Iwanashiro": "岩成村",
    "Kasenuma Park": "加瀬沼公園", "Kembuchi": "剣淵町", "Kitashiobara": "北塩原村",
    "Kunohe": "九戸村", "Minami Echizen": "南越前町", "Morotsuka": "諸塚村",
    "Nahari": "奈半利町", "PokéPark KANTO": "ポケパーク関東",
}

DOC_TITLE = "Pokemon - Plaques d'égout"
DOC_DESC  = (
    "Une carte de toutes les bouches d'égout Pokémon au Japon. <br>"
    "Toutes les informations proviennent directement du site web <br>"
    "https://local.pokemon.jp/en/manhole/ et les droits d'auteur leur appartiennent."
    "<br><br>Cette carte a été crée pour que les utilisateurs n'aient pas à chercher "
    "individuellement où se trouve chaque bouche d'égout et puissent planifier leurs "
    "déplacements pour voir celles à proximité plus facilement.<br>"
    "-------------------------------------------------------------<br><br>"
    "Evasions Rebelles<br>www.evasionsrebelles.com"
)
REGION_ORDER = [
    "Hokkaido", "Tohoku", "Kanto", "Chubu", "Kansaï",
    "Chugoku", "Shikoku", "Kyushu", "Okinawa", "Île d'Ogasawara",
]

PREFECTURE_TO_REGION = {
    "hokkaido": "Hokkaido",
    "aomori": "Tohoku", "iwate": "Tohoku", "miyagi": "Tohoku",
    "akita": "Tohoku", "yamagata": "Tohoku", "fukushima": "Tohoku",
    "ibaraki": "Kanto", "tochigi": "Kanto", "gunma": "Kanto",
    "saitama": "Kanto", "chiba": "Kanto", "tokyo": "Kanto", "kanagawa": "Kanto",
    "niigata": "Chubu", "toyama": "Chubu", "ishikawa": "Chubu", "fukui": "Chubu",
    "yamanashi": "Chubu", "nagano": "Chubu", "gifu": "Chubu",
    "shizuoka": "Chubu", "aichi": "Chubu",
    "mie": "Kansaï", "shiga": "Kansaï", "kyoto": "Kansaï", "osaka": "Kansaï",
    "hyogo": "Kansaï", "nara": "Kansaï", "wakayama": "Kansaï",
    "tottori": "Chugoku", "shimane": "Chugoku", "okayama": "Chugoku",
    "hiroshima": "Chugoku", "yamaguchi": "Chugoku",
    "tokushima": "Shikoku", "kagawa": "Shikoku", "ehime": "Shikoku", "kochi": "Shikoku",
    "fukuoka": "Kyushu", "saga": "Kyushu", "nagasaki": "Kyushu",
    "kumamoto": "Kyushu", "oita": "Kyushu", "miyazaki": "Kyushu", "kagoshima": "Kyushu",
    "okinawa": "Okinawa",
}
SPECIAL_OVERRIDES = {"ogasawara": {"prefecture_slug": "ogasawara",
                                    "region": "Île d'Ogasawara"}}

_thread_local = threading.local()

def get_session():
    s = getattr(_thread_local, "session", None)
    if s is None:
        s = requests.Session()
        s.headers.update(DEFAULT_HEADERS)
        _thread_local.session = s
    return s

_cache_lock = threading.Lock()

def load_json(path, default):
    if path.exists():
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            print(f"[!] {path.name} illisible, réinitialisé.", file=sys.stderr)
    return default

def save_json(path, data):
    with _cache_lock:
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        tmp.replace(path)

# ══════════════════════════════════════════════════════════════════════════
# PHASE 1 — RESOLVE
# ══════════════════════════════════════════════════════════════════════════

def fetch_prefecture_page(session, slug):
    resp = session.get(BASE_PREFECTURE.format(slug=slug), timeout=15)
    resp.raise_for_status()
    soup = BeautifulSoup(resp.text, "html.parser")
    results, seen = [], set()
    for a in soup.select('a[href*="/manhole/desc/"]'):
        m = MANHOLE_DESC_RE.search(a.get("href", ""))
        if not m or m.group(1) in seen:
            continue
        seen.add(m.group(1))
        label = a.get_text(strip=True)
        if not label:
            img = a.find("img")
            label = (img.get("alt") or "").strip() if img else ""
        results.append((m.group(1), label))
    return results


def phase_resolve(regions_cache, delay=0.5, retries=3, force=False,
                   resume_only=False):
    print("\n═══ PHASE 1 : RESOLVE (47 pages préfecture) ═══")
    session = get_session()
    all_slugs = sorted(PREFECTURE_TO_REGION.keys())
    known_before = set(regions_cache["manholes"].keys())

    if force:
        regions_cache["done_prefectures"] = []
        regions_cache["failed_prefectures"] = {}
        todo = all_slugs
        mode = "force (tout refaire)"
    elif resume_only:
        todo = [s for s in all_slugs if s not in regions_cache["done_prefectures"]]
        mode = f"resume-only ({len(regions_cache['done_prefectures'])} déjà traitées)"
    else:
        todo = all_slugs
        mode = "vérification systématique (revisite toutes les préfectures)"

    print(f"{len(todo)} préfecture(s) à traiter — mode : {mode}")
    print(f"{len(known_before)} plaques déjà connues avant ce run.")

    new_total = 0
    new_ids_this_run = []
    for idx, slug in enumerate(todo, start=1):
        region = PREFECTURE_TO_REGION[slug]
        print(f"  [{idx}/{len(todo)}] {slug} ({region})")
        entries, last_err = [], None
        for attempt in range(1, retries + 1):
            try:
                entries = fetch_prefecture_page(session, slug)
                last_err = None
                break
            except requests.RequestException as e:
                last_err = str(e)
                print(f"      tentative {attempt}/{retries} : {e}", file=sys.stderr)
                time.sleep(1.0 * attempt)

        if last_err is not None:
            regions_cache["failed_prefectures"][slug] = last_err
            save_json(REGIONS_CACHE, regions_cache)
            continue

        added = 0
        for mid, label in entries:
            if mid in regions_cache["manholes"]:
                continue
            override = SPECIAL_OVERRIDES.get(label.strip().lower())
            eff_slug = override["prefecture_slug"] if override else slug
            eff_region = override["region"] if override else region
            regions_cache["manholes"][mid] = {
                "url": f"https://local.pokemon.jp/en/manhole/desc/{mid}/",
                "prefecture_slug": eff_slug,
                "municipality_label": label or None,
                "region": eff_region,
            }
            added += 1
            new_ids_this_run.append(mid)
        print(f"      -> {len(entries)} plaques, {added} nouvelle(s)")

        if slug not in regions_cache["done_prefectures"]:
            regions_cache["done_prefectures"].append(slug)
        regions_cache["failed_prefectures"].pop(slug, None)
        save_json(REGIONS_CACHE, regions_cache)
        new_total += added
        time.sleep(delay)

    print(f"✅ RESOLVE : {len(regions_cache['manholes'])} plaques "
          f"({new_total} nouvelle(s))")
    if new_ids_this_run:
        print(f"   🆕 Nouvelles : {', '.join(sorted(new_ids_this_run, key=int))}")
    return new_total

# ══════════════════════════════════════════════════════════════════════════
# PHASE 2 — SCRAPE avec vérification à deux niveaux
# ══════════════════════════════════════════════════════════════════════════

def normalize_name(n):
    return unescape(n).strip().lower()

def load_pokemon_names():
    chosen = POKEMON_NAMES if POKEMON_NAMES.exists() else POKEMON_LEGACY
    if not chosen.exists():
        print(f"[!] Traductions FR/JP désactivées.", file=sys.stderr)
        return {}
    raw = json.loads(chosen.read_text(encoding="utf-8"))
    return {k: ({"fr": v, "jp": ""} if isinstance(v, str)
                else {"fr": v.get("fr", ""), "jp": v.get("jp", "")})
            for k, v in raw.items()}

POKEMON_NAMES_MAP = load_pokemon_names()
_MISSING_FR, _MISSING_JP = set(), set()

def translate_fr(name):
    fr = POKEMON_NAMES_MAP.get(normalize_name(name), {}).get("fr")
    if fr:
        return fr
    if name not in _MISSING_FR:
        _MISSING_FR.add(name)
        print(f"[!] FR manquant pour '{name}'", file=sys.stderr)
    return name

def translate_jp(name):
    jp = POKEMON_NAMES_MAP.get(normalize_name(name), {}).get("jp")
    if jp:
        return jp
    if name not in _MISSING_JP:
        _MISSING_JP.add(name)
        print(f"[!] JP manquant pour '{name}'", file=sys.stderr)
    return name


def split_pref_city(name):
    for sep in ("/", "／"):
        if sep in name:
            p, _, c = name.partition(sep)
            return p.strip(), c.strip()
    return None, name.strip()


POKEDEX_RE = re.compile(r"pokemon\.com/[a-z]{2}/pokedex/([a-z0-9\-]+)", re.I)
POKEDEX_IGNORE = {"pokédex", "pokedex"}
POKEMON_IMG_SELECTORS = [
    ".pokemon-list img[alt]", ".poke-list img[alt]", ".pokemon-icon img[alt]",
    ".pokemon-area img[alt]", "div.pokemon img[alt]", "ul.pokemon-name img[alt]",
    "div.detail .pokemon img[alt]", ".manhole-pokemon img[alt]",
]
POKEMON_ALT_BLACKLIST = {"", "Poké Lids", "Pokémon", "share", "close", "next", "prev"}


def extract_pokemon_names(soup):
    names, seen = [], set()
    for a in soup.select('a[href*="pokedex/"]'):
        m = POKEDEX_RE.search(a.get("href", ""))
        if not m:
            continue
        spans = a.find_all("span")
        n = spans[0].get_text(strip=True) if spans else a.get_text(strip=True)
        if not n:
            n = m.group(1).replace("-", " ").title()
        n = unescape(n).strip()
        if n.lower() in POKEDEX_IGNORE or n in seen:
            continue
        seen.add(n)
        names.append(n)
    if names:
        return names
    for sel in POKEMON_IMG_SELECTORS:
        alts = [unescape(i["alt"]).strip() for i in soup.select(sel)
                if unescape(i.get("alt", "")).strip() not in POKEMON_ALT_BLACKLIST]
        if alts:
            out, s = [], set()
            for a in alts:
                if a not in s:
                    s.add(a)
                    out.append(a)
            return out
    return []


def fetch_placemark_data(url):
    fetch_url = url if "is_modal=" in url else f"{url}?is_modal=1"
    resp = get_session().get(fetch_url, timeout=15)
    resp.raise_for_status()
    soup = BeautifulSoup(resp.text, "html.parser")

    heading = soup.select_one("div.heading h1") or soup.select_one("h1")
    name = heading.get_text(strip=True) if heading else None
    if not name:
        og = soup.select_one('meta[property="og:title"]')
        if og and og.get("content"):
            name = og["content"].split("｜")[0].strip()

    img = soup.select_one("div.heading img.mfp-swipe") or soup.select_one("div.heading img")
    image_url = urljoin(url, img["src"]) if img and img.get("src") else None
    if not image_url:
        og = soup.select_one('meta[property="og:image"]')
        if og and og.get("content"):
            image_url = og["content"]

    lat = lon = None
    gmap = soup.select_one('a[href*="maps.google"], a[href*="google.com/maps"], div.googlemap-link a')
    if gmap and gmap.get("href"):
        m = re.search(r"q=(-?[0-9.]+),(-?[0-9.]+)", gmap["href"])
        if m:
            lat, lon = m.group(1), m.group(2)

    if not name or not image_url or lat is None or lon is None:
        raise ValueError(f"Données incomplètes (name={name!r}, img={image_url!r}, "
                          f"lat={lat!r}, lon={lon!r})")

    pref, city = split_pref_city(name)
    return {
        "name": name, "prefecture": pref, "city": city,
        "image_url": image_url, "lat": lat, "lon": lon,
        "pokemon_names": extract_pokemon_names(soup),
        "page_hash": compute_page_hash(soup),
    }


def compute_page_hash(soup):
    parts = []
    heading = soup.select_one("div.heading h1") or soup.select_one("h1")
    if heading:
        parts.append("name:" + heading.get_text(strip=True))
    img = soup.select_one("div.heading img.mfp-swipe") or soup.select_one("div.heading img")
    if img and img.get("src"):
        parts.append("img:" + img["src"])
    gmap = soup.select_one('a[href*="maps.google"], a[href*="google.com/maps"], div.googlemap-link a')
    if gmap and gmap.get("href"):
        parts.append("gps:" + gmap["href"])
    for n in extract_pokemon_names(soup):
        parts.append("pk:" + n)
    return hashlib.sha256("\n".join(parts).encode("utf-8")).hexdigest()


def download_image(image_url: str, mid: str, force: bool,
                    quality: int, lossless: bool, method: int) -> dict:
    filename = f"icon-ci-{mid}.webp"
    path = IMAGES_DIR / filename

    if not force and path.exists():
        return {"filename": filename, "etag": None, "last_modified": None,
                "skipped": True}

    resp = get_session().get(image_url, timeout=20)
    resp.raise_for_status()
    etag = resp.headers.get("ETag")
    last_mod = resp.headers.get("Last-Modified")

    src = Image.open(io.BytesIO(resp.content)).convert("RGBA")
    src.thumbnail(ICON_SIZE, Image.LANCZOS)
    canvas = Image.new("RGBA", ICON_SIZE, (0, 0, 0, 0))
    offset = ((ICON_SIZE[0] - src.width) // 2,
              (ICON_SIZE[1] - src.height) // 2)
    canvas.paste(src, offset, src)

    out = io.BytesIO()
    canvas.save(out, format="WEBP", quality=quality,
                 lossless=lossless, method=method)
    path.write_bytes(out.getvalue())
    return {"filename": filename, "etag": etag, "last_modified": last_mod,
            "skipped": False}


def head_image(image_url: str) -> tuple:
    try:
        r = get_session().head(image_url, timeout=HEAD_TIMEOUT, allow_redirects=True)
        if r.status_code == 404:
            return "404", None
        if r.status_code == 200:
            return r.headers.get("ETag"), r.headers.get("Last-Modified")
    except requests.RequestException:
        pass
    return None, None


def classify_one(mid: str, manholes: dict, resume: dict, deep_check: bool) -> str:
    if mid not in resume["done"]:
        return "new"
    cached = resume["done"][mid]

    cached_url = cached.get("image_url", "")
    if cached_url:
        current_etag, current_lm = head_image(cached_url)
        if current_etag == "404":
            return "modified"
        if cached.get("image_etag") and current_etag and cached["image_etag"] != current_etag:
            return "modified"
        if cached.get("image_last_modified") and current_lm and cached["image_last_modified"] != current_lm:
            return "modified"

    if deep_check:
        try:
            r = get_session().get(
                f"{manholes[mid]['url']}?is_modal=1", timeout=15)
            r.raise_for_status()
            soup = BeautifulSoup(r.text, "html.parser")
            current_hash = compute_page_hash(soup)
            if cached.get("page_hash") and cached["page_hash"] != current_hash:
                return "modified"
        except requests.RequestException:
            pass

    return "same"


def classify_manholes(manholes: dict, resume: dict, deep_check: bool,
                       workers: int) -> dict:
    print("  Vérification des changements (L1/L2" +
          ("/L3" if deep_check else "") + ")...")
    todo = sorted(manholes.keys(), key=int)
    status = {}

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(classify_one, mid, manholes, resume, deep_check): mid
                   for mid in todo}
        for f in as_completed(futures):
            mid = futures[f]
            try:
                status[mid] = f.result()
            except Exception:
                status[mid] = "same"

    counts = Counter(status.values())
    print(f"    → {counts['new']} nouvelle(s), {counts['modified']} modifiée(s), "
          f"{counts['same']} inchangée(s)")
    return status


def phase_scrape(manholes, resume, force, workers, retries, delay,
                  quality, lossless, method, limit=None, deep_check=False):
    print("\n═══ PHASE 2 : SCRAPE (fiches + image unique WebP) ═══")
    IMAGES_DIR.mkdir(parents=True, exist_ok=True)

    all_ids = sorted(manholes.keys(), key=int)
    if limit:
        all_ids = all_ids[:limit]

    if force:
        todo = all_ids
        status = {mid: "new" for mid in all_ids}
        print(f"{len(all_ids)} plaques, toutes retraitées (--force).")
    else:
        status = classify_manholes(
            {mid: manholes[mid] for mid in all_ids}, resume, deep_check, workers)
        todo = [mid for mid in all_ids if status[mid] in ("new", "modified")]
        new_count = sum(1 for mid in all_ids if status[mid] == "new")
        mod_count = sum(1 for mid in all_ids if status[mid] == "modified")
        same_count = sum(1 for mid in all_ids if status[mid] == "same")
        print(f"{len(all_ids)} plaques : {new_count} nouvelle(s), "
              f"{mod_count} modifiée(s), {same_count} inchangée(s) → "
              f"{len(todo)} à (re)scraper.")

    modified_ids = []
    new_ids = [mid for mid in all_ids if status[mid] == "new"]

    if todo:
        total = len(todo)
        done_count = 0
        start = time.time()
        pending = {}

        def finalize(mid, pdata, img_result, src_url):
            nonlocal done_count
            resume["done"][mid] = {
                "name": pdata["name"],
                "prefecture": pdata.get("prefecture"),
                "city": pdata.get("city"),
                "lat": pdata["lat"], "lon": pdata["lon"],
                "image_file": img_result["filename"],
                "image_url": f"{GITHUB_RAW_BASE}/icon-ci-{mid}.webp", # URL GitHub (image déjà téléchargée et commitée dans ce même run)
                "image_etag": img_result.get("etag"),
                "image_last_modified": img_result.get("last_modified"),
                "page_hash": pdata.get("page_hash"),
                "source_url": src_url,
                "region": manholes[mid]["region"],
                "pokemon_names": pdata.get("pokemon_names", []),
            }
            resume["failed"].pop(mid, None)
            done_count += 1
            if done_count % 25 == 0 or done_count == total:
                save_json(RESUME_CACHE, resume)
            elapsed = time.time() - start
            eta = (elapsed / done_count) * (total - done_count) if done_count else 0
            print(f"  [{done_count}/{total}] {mid} OK | {int(elapsed)}s, ETA ~{int(eta)}s")

        try:
            with ThreadPoolExecutor(max_workers=workers) as pool:
                for idx, mid in enumerate(todo, start=1):
                    url = manholes[mid]["url"]
                    pdata, last_err = None, None
                    for attempt in range(1, retries + 1):
                        try:
                            pdata = fetch_placemark_data(url)
                            last_err = None
                            break
                        except (requests.RequestException, ValueError) as e:
                            last_err = str(e)
                            time.sleep(0.5 * (2 ** (attempt - 1)))

                    if last_err is not None:
                        resume["failed"][mid] = {"url": url, "error": last_err}
                        save_json(RESUME_CACHE, resume)
                        print(f"  [{idx}/{total}] {mid} ÉCHEC page : {last_err}", file=sys.stderr)
                        if delay:
                            time.sleep(delay)
                        continue

                    if not pdata.get("prefecture"):
                        slug = manholes[mid].get("prefecture_slug")
                        if slug:
                            pdata["prefecture"] = slug.replace("_", " ").capitalize()

                    # mid est forcément "new", "modified" (ou --force global) ici,
                    # puisqu'il vient de `todo` : on force donc toujours le
                    # re-téléchargement de l'image, même si un fichier local du
                    # même nom existe déjà (ex. images_webp/ restauré par checkout).
                    fut = pool.submit(download_image, pdata["image_url"], mid,
                                       True, quality, lossless, method)
                    pending[fut] = (mid, pdata, url)

                    for f in [f for f in pending if f.done()]:
                        m, pd, u = pending.pop(f)
                        try:
                            img_result = f.result()
                        except Exception as e:
                            resume["failed"][m] = {"url": u, "error": f"image: {e}"}
                            save_json(RESUME_CACHE, resume)
                            continue
                        finalize(m, pd, img_result, u)

                    if delay:
                        time.sleep(delay)

                print(f"\n⏳ Attente de {len(pending)} image(s)…")
                for f in as_completed(pending):
                    m, pd, u = pending.pop(f)
                    try:
                        img_result = f.result()
                    except Exception as e:
                        resume["failed"][m] = {"url": u, "error": f"image: {e}"}
                        save_json(RESUME_CACHE, resume)
                        continue
                    finalize(m, pd, img_result, u)

        except KeyboardInterrupt:
            print(f"\n[interrompu] Cache sauvegardé.", file=sys.stderr)
            save_json(RESUME_CACHE, resume)
            sys.exit(1)

        save_json(RESUME_CACHE, resume)
    
    # ── Remplacement des URLs pour les plaques inchangées ──────────────────
    same_count_updated = 0
    for mid in all_ids:
        if status[mid] == "modified":
            modified_ids.append(mid)
        
        if status[mid] in ("new", "modified"):
            # On garde l'URL de base (site officiel)
            continue
        
        # status == "same"
        if mid in resume["done"]:
            resume["done"][mid]["image_url"] = f"{GITHUB_RAW_BASE}/icon-ci-{mid}.webp"
            same_count_updated += 1
            
    save_json(RESUME_CACHE, resume)
    
    print(f"✅ SCRAPE : {len(resume['done'])} plaques en cache.")
    if same_count_updated:
        print(f"   🔄 {same_count_updated} plaque(s) inchangée(s) : image_url pointée vers GitHub.")
    
    # Affichage explicite des modifications
    if new_ids or modified_ids:
        print(f"\n⚠️  ATTENTION - MODIFICATIONS DÉTECTÉES :")
        if new_ids:
            print(f"   🆕 {len(new_ids)} nouvelle(s) plaque(s) (URL GitHub) :")
            print(f"      {', '.join(sorted(new_ids, key=int))}")
        if modified_ids:
            print(f"   🔧 {len(modified_ids)} plaque(s) modifiée(s) (URL GitHub) :")
            print(f"      {', '.join(sorted(modified_ids, key=int))}")
    else:
        print("   ✅ Aucune nouveauté ou modification détectée ce run.")

# ══════════════════════════════════════════════════════════════════════════
# PHASE 3 — KANJI
# ══════════════════════════════════════════════════════════════════════════

class GeoNamesDB:
    def __init__(self, geonames_file):
        self.db_exact = defaultdict(list)
        self.db_all = []
        if not Path(geonames_file).exists():
            print(f"⚠️  {Path(geonames_file).name} absent : phases exact/fuzzy "
                  f"désactivées (Wikipédia seulement).")
            return
        print(f"📂 Chargement GeoNames : {Path(geonames_file).name}")
        rows = kanji_ok = 0
        with open(geonames_file, "r", encoding="utf-8") as f:
            for row in csv.reader(f, delimiter="\t"):
                rows += 1
                if len(row) < 4:
                    continue
                name, ascii_name, alt_str = row[1].strip(), row[2].strip(), row[3].strip()
                if not alt_str:
                    continue
                kanji = next((p.strip() for p in alt_str.split(",")
                              if p.strip() and is_kanji(p.strip())), None)
                if kanji:
                    kanji_ok += 1
                    self.db_exact[name].append(kanji)
                    if ascii_name and ascii_name != name:
                        self.db_exact[ascii_name].append(kanji)
                    self.db_all.append({"name": name, "ascii": ascii_name, "kanji": kanji})
        print(f"✅ GeoNames : {rows} lignes, {kanji_ok} kanji, "
              f"{len(self.db_exact)} noms exacts.")

    def lookup_exact(self, city):
        if city in self.db_exact:
            return self.db_exact[city][0]
        return None

    def lookup_fuzzy(self, city, threshold=0.85):
        variants = [city]
        for suf in ADMIN_SUFFIXES:
            if city.endswith(suf):
                variants.append(city[:-len(suf)])
                break
        best, best_ratio, best_kanji = None, 0, None
        for var in variants:
            for e in self.db_all:
                if not e["ascii"]:
                    continue
                r = difflib.SequenceMatcher(None, var.lower(), e["ascii"].lower()).ratio()
                if r > best_ratio and r >= threshold:
                    best, best_ratio, best_kanji = e["ascii"], r, e["kanji"]
        return (best_kanji, f"fuzzy {best_ratio:.0%}") if best else (None, None)


def is_kanji(text):
    if any(c.isascii() and c.isalpha() for c in text):
        return False
    return any(0x4E00 <= ord(c) <= 0x9FFF for c in text)


def wiki_lookup(city):
    try:
        r = requests.get(
            "https://en.wikipedia.org/w/api.php",
            params={"action": "query", "titles": city, "prop": "langlinks",
                    "lllang": "ja", "format": "json", "redirects": 1},
            headers={"User-Agent": "KML-Kanji-Enricher/11.0"},
            timeout=WIKI_TIMEOUT,
        )
        r.raise_for_status()
        for page in r.json().get("query", {}).get("pages", {}).values():
            ll = page.get("langlinks")
            if ll:
                return ll[0].get("*")
    except requests.RequestException:
        pass
    time.sleep(WIKI_DELAY)
    return None


def phase_kanji(resume, force=False):
    print("\n═══ PHASE 3 : KANJI (enrichissement villes) ═══")
    kanji_db = load_json(KANJI_CACHE, {})
    for city, kanji in MANUAL_CITIES.items():
        if city not in kanji_db:
            kanji_db[city] = {"kanji": kanji, "source": "manual"}

    cities = {}
    for mid, data in resume["done"].items():
        c = data.get("city")
        if c:
            cities.setdefault(c, []).append(mid)

    if not cities:
        print("✅ KANJI : aucune ville à traiter.")
        return

    to_resolve = [c for c in cities if c not in kanji_db or not kanji_db[c].get("kanji")]
    print(f"{len(cities)} ville(s) unique(s), {len(to_resolve)} à résoudre "
          f"({len(cities) - len(to_resolve)} déjà en cache).")

    geonames = GeoNamesDB(GEONAMES) if to_resolve else None
    new_entries = 0
    not_found = []

    def save_if_needed(force_flush=False):
        nonlocal new_entries
        if force_flush or new_entries >= KANJI_SAVE_INTERVAL:
            save_json(KANJI_CACHE, kanji_db)
            new_entries = 0

    iterator = to_resolve
    if tqdm:
        iterator = tqdm(to_resolve, desc="Kanji", unit="ville")

    for city in iterator:
        kanji, source = None, None
        entry = kanji_db.get(city)
        if entry and entry.get("kanji"):
            kanji, source = entry["kanji"], entry.get("source", "json")
        if not kanji and geonames:
            kanji = geonames.lookup_exact(city)
            if kanji:
                source = "exact"
        if not kanji and geonames:
            kanji, _how = geonames.lookup_fuzzy(city)
            if kanji:
                source = "fuzzy"
        if not kanji:
            kanji = wiki_lookup(city)
            if kanji:
                source = "wikipedia"

        if kanji:
            kanji_db[city] = {"kanji": kanji, "source": source}
            new_entries += 1
            save_if_needed()
            if tqdm:
                tqdm.write(f"  ✓ {city:30} → {kanji} [{source}]")
            else:
                print(f"  ✓ {city:30} → {kanji} [{source}]")
        else:
            not_found.append(city)
            if tqdm:
                tqdm.write(f"  ✗ {city:30} - introuvable")
            else:
                print(f"  ✗ {city:30} - introuvable")

    save_if_needed(force_flush=True)

    resolved = 0
    for city, mids in cities.items():
        entry = kanji_db.get(city)
        kanji = entry.get("kanji") if entry else None
        for mid in mids:
            if kanji:
                resume["done"][mid]["city_kanji"] = kanji
                resolved += 1
    save_json(RESUME_CACHE, resume)

    print(f"\n✅ KANJI : {len(cities) - len(not_found)}/{len(cities)} villes résolues "
          f"→ {resolved} plaque(s) enrichie(s).")
    if not_found:
        KANJI_MISSING.parent.mkdir(exist_ok=True)
        with open(KANJI_MISSING, "w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["City", "Status", "Notes"])
            for c in sorted(not_found):
                w.writerow([c, "Non trouvée", "Recherche manuelle requise"])
        print(f"📝 {len(not_found)} ville(s) non trouvée(s) → {KANJI_MISSING}")

# ══════════════════════════════════════════════════════════════════════════
# PHASE 4 — GÉNÉRATION KML + JSON
# ══════════════════════════════════════════════════════════════════════════

def placemark_name_parts(data):
    names = data.get("pokemon_names") or []
    if names:
        return (", ".join(translate_fr(n) for n in names),
                ", ".join(names),
                ", ".join(translate_jp(n) for n in names))
    return data["name"], data["name"], data["name"]


def placemark_display_name(data):
    names = data.get("pokemon_names") or []
    if names:
        fr, en, _ = placemark_name_parts(data)
        return f"{fr}-{en}"
    return data["name"]


def placemark_record(mid, data):
    fr, en, jp = placemark_name_parts(data)
    return {
        "id": str(mid),
        "region": data.get("region", "Inconnue"),
        "name": placemark_display_name(data),
        "category": "Pokelid",
        "source_url": data["source_url"],
        "name_en": en, "name_fr": fr, "name_jp": jp,
        "prefecture": data.get("prefecture") or "",
        "city": data.get("city") or "",
        "city_kanji": data.get("city_kanji") or "",
        "pokemon_names": data.get("pokemon_names") or [],
        "lat": float(data["lat"]), "lon": float(data["lon"]),
        "image_file": data["image_file"],
        "image_url": data.get("image_url") or "",
    }


def grouped_records(done):
    by_region = {}
    for mid, data in done.items():
        by_region.setdefault(data.get("region", "Inconnue"), []).append(
            placemark_record(mid, data))
    ordered = [r for r in REGION_ORDER if r in by_region]
    ordered += sorted(r for r in by_region if r not in REGION_ORDER)
    return [(r, sorted(by_region[r], key=lambda x: int(x["id"]))) for r in ordered]


def style_block(mid, img_rel):
    return f'''    <Style id="icon-ci-{mid}-normal"><IconStyle><scale>1.1</scale><Icon><href>{img_rel}</href></Icon></IconStyle><LabelStyle><scale>0</scale></LabelStyle></Style>
    <Style id="icon-ci-{mid}-highlight"><IconStyle><scale>1.1</scale><Icon><href>{img_rel}</href></Icon></IconStyle><LabelStyle><scale>1.1</scale></LabelStyle></Style>
    <StyleMap id="icon-ci-{mid}"><Pair><key>normal</key><styleUrl>#icon-ci-{mid}-normal</styleUrl></Pair><Pair><key>highlight</key><styleUrl>#icon-ci-{mid}-highlight</styleUrl></Pair></StyleMap>
'''


def placemark_block(rec):
    mid = rec["id"]
    desc_img = rec["image_url"] or f'images_webp/{rec["image_file"]}'
    desc = (f'<img src="{escape(desc_img)}" height="200" width="200" />'
            f'<br><br>{rec["source_url"]}<br>{rec["lat"]},{rec["lon"]}')
    city_display = rec["city"]
    if rec["city_kanji"]:
        city_display = f'{rec["city"]} ({rec["city_kanji"]})'
    return f'''      <Placemark>
        <name>{escape(rec["name"])}</name>
        <description><![CDATA[{desc}]]></description>
        <styleUrl>#icon-ci-{mid}</styleUrl>
        <ExtendedData>
          <Data name="Category"><value><![CDATA[{rec["category"]}]]></value></Data>
          <Data name="source_url"><value><![CDATA[{rec["source_url"]}]]></value></Data>
          <Data name="Name (En)"><value><![CDATA[{rec["name_en"]}]]></value></Data>
          <Data name="Nom (FR)"><value><![CDATA[{rec["name_fr"]}]]></value></Data>
          <Data name="名前 (JP)"><value><![CDATA[{rec["name_jp"]}]]></value></Data>
          <Data name="Prefecture"><value><![CDATA[{escape(rec["prefecture"])}]]></value></Data>
          <Data name="City"><value><![CDATA[{escape(city_display)}]]></value></Data>
          <Data name="city_kanji"><value><![CDATA[{escape(rec["city_kanji"])}]]></value></Data>
        </ExtendedData>
        <Point><coordinates>{rec["lon"]},{rec["lat"]},0</coordinates></Point>
      </Placemark>
'''


def build_kml_and_json(done):
    grouped = grouped_records(done)
    styles, folders, all_records = [], [], []
    for region, records in grouped:
        body = []
        for rec in records:
            # On utilise l'image_url de la rec (qui contient soit le site officiel, soit GitHub)
            img_rel = rec["image_url"] or f'images_webp/{rec["image_file"]}'
            styles.append(style_block(rec["id"], img_rel))
            body.append(placemark_block(rec))
            all_records.append(rec)
        folders.append(f'    <Folder>\n      <name>{escape(region)}</name>\n'
                        + "".join(body) + '    </Folder>\n')

    kml = ('<?xml version="1.0" encoding="UTF-8"?>\n'
           '<kml xmlns="http://www.opengis.net/kml/2.2">\n  <Document>\n'
           f'    <name><![CDATA[{DOC_TITLE}]]></name>\n'
           f'    <description><![CDATA[{DOC_DESC}]]></description>\n'
           + "".join(styles) + "".join(folders)
           + '  </Document>\n</kml>\n')

    js = {"document": {"title": DOC_TITLE, "description": DOC_DESC},
          "regions": [r for r, _ in grouped],
          "count": len(all_records),
          "placemarks": all_records}
    return kml, js


def phase_generate(done):
    print("\n═══ PHASE 4 : GÉNÉRATION KML + JSON ═══")
    kml, js = build_kml_and_json(done)
    KML_FILE.write_text(kml, encoding="utf-8")
    JSON_FILE.write_text(json.dumps(js, ensure_ascii=False, indent=2), encoding="utf-8")
    kanji_count = sum(1 for p in js["placemarks"] if p["city_kanji"])
    print(f"✅ {len(done)} plaques -> {KML_FILE.name} + {JSON_FILE.name} "
          f"({len(js['regions'])} régions, {kanji_count} avec kanji)")

# ══════════════════════════════════════════════════════════════════════════
# Mode --inspect
# ══════════════════════════════════════════════════════════════════════════

def mode_inspect(mid):
    url = PROBE_URL.format(id=mid)
    r = get_session().get(url, timeout=15)
    r.raise_for_status()
    soup = BeautifulSoup(r.text, "html.parser")
    print(f"--- <img alt> sur {url} ---")
    for img in soup.find_all("img"):
        if img.get("alt", "").strip():
            print(f"  alt={img['alt']!r} class={' '.join(img.get('class', []))!r}")
    print(f"\n--- Liens pokedex ---")
    for a in soup.select('a[href*="pokedex/"]'):
        print(f"  {a.get('href')!r} -> {[s.get_text(strip=True) for s in a.find_all('span')]}")
    print(f"\n--- extract_pokemon_names() ---")
    print(extract_pokemon_names(soup))

# ══════════════════════════════════════════════════════════════════════════
# Main
# ══════════════════════════════════════════════════════════════════════════

def main():
    p = argparse.ArgumentParser(
        description="Pipeline fusionné 01+02+03+04 avec vérification à deux "
                    "niveaux. Un nouveau lancement CHERCHE les nouveautés et "
                    "les modifications (revisite les 47 pages + L2 sur les "
                    "images + L3 optionnel sur les fiches).")
    p.add_argument("--force", action="store_true",
                    help="Tout refaire (ignore tous les caches).")
    p.add_argument("--resume-only", action="store_true",
                    help="Ne traite que les préfectures absentes de "
                         "done_prefectures (reprise d'un run interrompu). "
                         "Par défaut, toutes les préfectures sont revisitées.")
    p.add_argument("--no-resolve", action="store_true", help="Saute la phase 1.")
    p.add_argument("--no-kanji", action="store_true",
                    help="Désactive l'enrichissement kanji.")
    p.add_argument("--deep-check", action="store_true",
                    help="Active L3 (hash des fiches HTML, plus lent mais "
                         "détecte les changements de titre/GPS/Pokémon).")
    p.add_argument("--emit-regions", action="store_true",
                    help="Écrit aussi regions.json (compat 04).")
    p.add_argument("--dry-run", action="store_true", help="N'écrit rien.")
    p.add_argument("--workers", type=int, default=DEFAULT_WORKERS)
    p.add_argument("--fast", action="store_true")
    p.add_argument("--limit", type=int, default=None)
    p.add_argument("--inspect", metavar="ID")
    p.add_argument("--quality", type=int, default=WEBP_QUALITY,
                    help=f"Qualité WebP 0-100 (défaut: {WEBP_QUALITY})")
    p.add_argument("--lossless", action="store_true",
                    help="WebP sans perte")
    p.add_argument("--method", type=int, default=WEBP_METHOD,
                    help=f"Effort d'encodage WebP 0-6 (défaut: {WEBP_METHOD})")
    args = p.parse_args()

    if args.fast:
        args.workers = max(args.workers, 16)

    if args.inspect:
        mode_inspect(args.inspect)
        return

    t0 = time.time()
    print("╔══════════════════════════════════════════════════════════════════╗")
    print("║  Poké Lids — pipeline 01+02+03+04 (vérif. 2 niveaux)             ║")
    print("║  Livrables : pokelid.kml, pokelid.json, images_webp/             ║")
    print("╚══════════════════════════════════════════════════════════════════╝")
    if args.dry_run:
        print("MODE --dry-run : aucune écriture.")

    if not args.dry_run:
        CACHE_DIR.mkdir(exist_ok=True)

    regions_cache = load_json(REGIONS_CACHE, {
        "done_prefectures": [], "manholes": {}, "failed_prefectures": {}})
    if not {"done_prefectures", "manholes", "failed_prefectures"}.issubset(regions_cache):
        regions_cache = {"done_prefectures": [], "manholes": {}, "failed_prefectures": {}}

    resume = load_json(RESUME_CACHE, {"done": {}, "failed": {}})
    if "done" not in resume or "failed" not in resume:
        resume = {"done": {}, "failed": {}}

    # PHASE 1
    if args.no_resolve:
        print(f"\n⏭  PHASE 1 sautée (--no-resolve).")
    elif not args.dry_run:
        phase_resolve(regions_cache, force=args.force,
                       resume_only=args.resume_only)
    else:
        print("\n[DRY] PHASE 1 RESOLVE serait exécutée.")

    # PHASE 2 : SCRAPE
    manholes = regions_cache["manholes"]
    if not manholes:
        print("\n❌ Aucune plaque — abandon.", file=sys.stderr)
        sys.exit(1)
    if not args.dry_run:
        phase_scrape(manholes, resume, force=args.force,
                      workers=args.workers, retries=3, delay=0.3,
                      quality=args.quality, lossless=args.lossless,
                      method=args.method, limit=args.limit,
                      deep_check=args.deep_check)
    else:
        print(f"\n[DRY] PHASE 2 SCRAPE serait exécutée.")

    # PHASE 3 : KANJI
    if args.no_kanji:
        print("\n⏭  PHASE 3 KANJI sautée (--no-kanji).")
    elif not args.dry_run:
        phase_kanji(resume, force=args.force)
    else:
        print("\n[DRY] PHASE 3 KANJI serait exécutée.")

    # PHASE 4 : GÉNÉRATION
    if not args.dry_run:
        phase_generate(resume["done"])
        if args.emit_regions:
            REGIONS_TMP.write_text(
                json.dumps(manholes, ensure_ascii=False, indent=2), encoding="utf-8")
            print(f"ℹ️  regions.json émis pour compat 04 : {REGIONS_TMP.name}")
    else:
        print(f"\n[DRY] PHASE 4 GÉNÉRATION : pokelid.kml + pokelid.json.")

    # Résumé
    elapsed = time.time() - t0
    print("\n" + "═" * 60)
    print(f"✅ Terminé en {int(elapsed // 60)}m{int(elapsed % 60):02d}s")
    print(f"   pokelid.kml  : {KML_FILE.name}")
    print(f"   pokelid.json : {JSON_FILE.name}")
    print(f"   images_webp/ : {len(list(IMAGES_DIR.glob('icon-ci-*.webp')))} fichiers WebP")
    kanji_count = sum(1 for d in resume["done"].values() if d.get("city_kanji"))
    print(f"   kanji        : {kanji_count}/{len(resume['done'])} plaques enrichies")
    if resume["failed"]:
        print(f"   ⚠️  {len(resume['failed'])} échec(s)")
    if regions_cache["failed_prefectures"]:
        print(f"   ⚠️  {len(regions_cache['failed_prefectures'])} préfecture(s) en échec")


if __name__ == "__main__":
    main()
