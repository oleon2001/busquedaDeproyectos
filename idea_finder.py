#!/usr/bin/env python3
"""Termometro de Proyectos v3 - cazador de demanda real.

Clasifica cada post como DEMANDA (comprador busca algo), OFERTA (freelancer se
vende) o TENDENCIA (articulo/repo), extrae el tipo de proyecto y presupuesto, y
rankea por OPORTUNIDAD = demanda vs competencia vs presupuesto.

Fuentes:
  - Reddit   via api.redditapis.com   (REDDITAPIS_KEY)
  - Hacker News (Algolia)             sin key
  - Dev.to / RemoteOK / GitHub        sin key
  - Gemini   opcional para extraccion (--ai, GEMINI_API_KEY)

Uso:
  python idea_finder.py                 # online + dashboard.html (usa cache)
  python idea_finder.py --refresh       # ignora cache
  python idea_finder.py --offline       # autotest + dashboard con datos de muestra
  python idea_finder.py --ai            # activa extraccion con Gemini
  python idea_finder.py --budget 4      # tope de llamadas nuevas a Reddit
  python idea_finder.py --top 20        # filas en la tabla
"""
import argparse
import hashlib
import html as html_mod
import json
import os
import random
import re
import statistics
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from pathlib import Path

BASE = Path(__file__).resolve().parent
CACHE = BASE / "cache"
DASHBOARD = BASE / "dashboard.html"

UA = "projfinder/0.2 (idea thermometer; local personal use)"

CONFIG = {
    "subreddits": [
        "forhire", "freelance", "SaaS", "startups", "Entrepreneur", "webdev",
        "smallbusiness", "selfhosted", "jobbit", "DesignJobs", "ProgrammingJobs",
    ],
    "hn_threads": ["Freelancer? Seeking freelancer?", "Who is hiring?"],
    "hn_queries": ["looking for developer", "need an app built", "hiring developer"],
    "devto_tags": ["webdev", "programming", "ai", "startup"],
    "github_days": 30,
    "github_min_stars": 40,
    "ttl_hours": 24,
    "timeout": 25,
    "max_reddit_calls": 11,
    "recency_days": 45,
    "weights": {"budget": 0.5, "recency": 0.5, "engagement_div": 100.0},
    "gemini_model": "gemini-3.5-flash-lite",
    "gemini_max_calls": 300,
    "gemini_workers": 5,
    "gemini_body_chars": 1500,
}

TAXONOMY = {
    "landing/website": ["landing page", "website", "web page", "webpage", "web site", "sitio web", "pagina web"],
    "web scraper": ["scraper", "scraping", "scrape", "crawler"],
    "automation": ["automation", "automate", "workflow", "zapier", "make.com", "n8n"],
    "AI chatbot": ["chatbot", "chat bot", "ai agent", "gpt", "llm", "rag", "openai", "assistant bot"],
    "dashboard": ["dashboard", "admin panel", "analytics panel", "reporting"],
    "mobile app": ["mobile app", "ios app", "android app", "react native", "flutter app", "app store"],
    "ecommerce": ["ecommerce", "e-commerce", "shopify", "woocommerce", "tienda online", "online store"],
    "api/integration": ["api integration", "rest api", "webhook", "integration", "integrate", "api "],
    "CRM/ops": ["crm", "hubspot", "salesforce", "pipeline"],
    "SEO/marketing": ["seo", "google ads", "ppc", "marketing", "traffic", "sem"],
    "design/logo": ["logo", "branding", "graphic design", "designer", "figma", "ui design"],
    "video/editing": ["video editing", "video editor", "youtube video", "tiktok", "reels", "editing"],
    "data/etl": ["etl", "data pipeline", "data engineer", "data analysis", "dataset", "data scraping"],
    "wordpress": ["wordpress", "elementor", "wp "],
    "devops/infra": ["devops", "kubernetes", "docker", "aws", "cloud", "infrastructure", "ci/cd"],
    "plugin/extension": ["chrome extension", "browser extension", "vscode extension", "plugin", "addon"],
    "content/copy": ["copywriting", "content writer", "blog writer", "ghostwriter", "copywriter"],
    "virtual assistant": ["virtual assistant", "assistant", "data entry", "admin support"],
}

MONEY_RE = re.compile(
    r"(?:\$|usd|eur|\u20ac|\u00a3)\s?(\d[\d,]*\.?\d*)"
    r"|(\d[\d,]*\.?\d*)\s?(?:usd|eur|\u20ac|\u00a3|dollars|\bk\b)"
    r"|\bbudget\b|\brate\b|\bsalary\b|/hr\b|/hour\b|per hour|\bhourly\b",
    re.IGNORECASE,
)
BUDGET_NUM_RE = re.compile(
    r"(?:\$|usd|eur|\u20ac|\u00a3)\s?(\d[\d,]*\.?\d*)"
    r"|(\d[\d,]*\.?\d*)\s?(?:usd|eur|\u20ac|\u00a3|dollars)",
    re.IGNORECASE,
)
BUDGET_RANGE_RE = re.compile(
    r"(?:\$|usd|eur|\u20ac|\u00a3)\s?(\d[\d,]*\.?\d*)\s?(?:-|\u2013|to)\s?\$?\s?(\d[\d,]*\.?\d*)",
    re.IGNORECASE,
)
PERIODS = (
    ("hourly", re.compile(r"/\s?h(r|our)?\b|per hour|hourly|\bhr\b|\bhour\b", re.I)),
    ("monthly", re.compile(r"/\s?mo(nth)?\b|per month|monthly|\bmo\b|\bmonth\b", re.I)),
)
DEMAND_RE = re.compile(r"\[hiring\]|\bhiring\b|\blooking for\b|\bneed\b|\bbuild me\b|seeking freelancer|\blooking to build\b", re.I)
OFFER_RE = re.compile(r"\[for hire\]|\bfor hire\b|\bi can\b|\bi will\b|\bi build\b|\bi develop\b|\bmy services\b|available for", re.I)


# ---------------------------------------------------------------- utilidades

def load_env():
    path = BASE / ".env"
    if not path.exists():
        return
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, val = line.split("=", 1)
        os.environ.setdefault(key.strip(), val.strip().strip('"').strip("'"))


def clean(text):
    return html_mod.unescape(re.sub(r"<[^>]+>", " ", text or "")).strip()


def http_get(url, headers=None):
    hdrs = {"User-Agent": UA, "Accept": "application/json"}
    if headers:
        hdrs.update(headers)
    req = urllib.request.Request(url, headers=hdrs)
    with urllib.request.urlopen(req, timeout=CONFIG["timeout"]) as resp:
        return json.loads(resp.read().decode("utf-8", "replace"))


def http_post_json(url, payload, headers=None):
    hdrs = {"User-Agent": UA, "Content-Type": "application/json"}
    if headers:
        hdrs.update(headers)
    req = urllib.request.Request(url, data=json.dumps(payload).encode("utf-8"), headers=hdrs)
    with urllib.request.urlopen(req, timeout=CONFIG["timeout"]) as resp:
        return json.loads(resp.read().decode("utf-8", "replace"))


def _retry(call, retries, label):
    last = None
    for attempt in range(retries):
        try:
            return call()
        except urllib.error.HTTPError as exc:
            last = exc
            if exc.code in (429, 500, 502, 503, 504) and attempt < retries - 1:
                wait = float(exc.headers.get("Retry-After") or 0) or (2 ** attempt + random.random())
                print(f"[retry] {label} {exc.code}, esperando {wait:.1f}s")
                time.sleep(wait)
                continue
            raise
        except Exception as exc:  # noqa: BLE001
            last = exc
            if attempt < retries - 1:
                time.sleep(2 ** attempt + random.random())
                continue
            raise
    raise last if last is not None else RuntimeError(f"fallo en {label}")


def http_get_retry(url, headers=None, retries=3):
    return _retry(lambda: http_get(url, headers), retries, url[:60])


def http_post_json_retry(url, payload, headers=None, retries=4):
    return _retry(lambda: http_post_json(url, payload, headers), retries, "gemini")


def cache_path(name):
    return CACHE / f"{name}.json"


def cache_get(name, ttl_hours):
    path = cache_path(name)
    if not path.exists():
        return None
    try:
        blob = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    if ttl_hours is not None and time.time() - blob.get("ts", 0) > ttl_hours * 3600:
        return None
    return blob.get("data")


def cache_put(name, data):
    CACHE.mkdir(exist_ok=True)
    cache_path(name).write_text(json.dumps({"ts": time.time(), "data": data}), encoding="utf-8")


def cached_fetch(name, url, refresh, headers=None):
    if not refresh:
        data = cache_get(name, CONFIG["ttl_hours"])
        if data is not None:
            return data
    try:
        data = http_get_retry(url, headers)
    except Exception as exc:  # noqa: BLE001
        print(f"[warn] {name}: {exc}")
        stale = cache_get(name, None)
        return stale if stale is not None else {}
    cache_put(name, data)
    return data


def to_epoch(value):
    if isinstance(value, (int, float)):
        return int(value)
    if not value:
        return 0
    try:
        return int(datetime.fromisoformat(str(value).replace("Z", "+00:00")).timestamp())
    except ValueError:
        return 0


def norm(source, title, text, url, up=0, com=0, created=0):
    return {
        "source": source,
        "title": clean(title),
        "text": clean(text),
        "url": url or "",
        "upvotes": int(up or 0),
        "comments": int(com or 0),
        "created": to_epoch(created),
    }


def slug(text):
    return re.sub(r"\W+", "_", text.lower())[:40]


def has_money(text):
    return bool(MONEY_RE.search(text))


# ------------------------------------------------------------------ analisis

def classify(rec):
    """DEMANDA (comprador) / OFERTA (freelancer) / TENDENCIA (articulo/repo)."""
    if rec["source"] in ("devto", "github"):
        return "TENDENCIA"
    title = rec["title"].lower()
    if "[for hire]" in title:
        return "OFERTA"
    if "[hiring]" in title:
        return "DEMANDA"
    blob = (title + " " + rec["text"].lower())
    demand, offer = len(DEMAND_RE.findall(blob)), len(OFFER_RE.findall(blob))
    if demand > offer:
        return "DEMANDA"
    if offer > demand:
        return "OFERTA"
    return "TENDENCIA"


def parse_budget(text):
    t = text.lower()
    t = re.sub(r"(\d[\d,]*\.?\d*)\s*k\b", lambda m: str(float(m.group(1).replace(",", "")) * 1000), t)
    nums = []
    for match in BUDGET_RANGE_RE.finditer(t):
        for group in match.groups():
            try:
                nums.append(float(group.replace(",", "")))
            except (ValueError, AttributeError):
                pass
    for match in BUDGET_NUM_RE.finditer(t):
        raw = match.group(1) or match.group(2)
        try:
            nums.append(float(raw.replace(",", "")))
        except ValueError:
            pass
    if not nums:
        return None
    period = "fixed"
    for name, pattern in PERIODS:
        if pattern.search(t):
            period = name
            break
    return {"min": min(nums), "max": max(nums), "period": period}


def detect_types(rec):
    blob = (rec["title"] + " " + rec["text"]).lower()
    total = rec["upvotes"] + rec["comments"]
    hits = [(ptype, blob.count(trigger)) for ptype, triggers in TAXONOMY.items()
            for trigger in triggers if trigger in blob]
    if not hits:
        return ["otro"]
    return [ptype for ptype, _ in sorted(hits, key=lambda h: -h[1])[:2]]


GEMINI_URL = ("https://generativelanguage.googleapis.com/v1beta/models/"
              "{model}:generateContent?key={key}")
GEMINI_PROMPT = """Eres analista de encargos freelance. Devuelve SOLO JSON valido:
{{"tipo":"<landing/website|web scraper|automation|AI chatbot|dashboard|mobile app|ecommerce|api/integration|CRM/ops|SEO/marketing|design/logo|video/editing|data/etl|wordpress|devops/infra|plugin/extension|content/copy|virtual assistant|otro>",
"stack":["..."],"presupuesto_min":<num|null>,"presupuesto_max":<num|null>,"moneda":"USD|EUR|otro|null","periodo":"hourly|monthly|fixed|null",
"modalidad":"freelance|producto|empleo","resumen":"max 12 palabras","complejidad":"baja|media|alta"}}
Post: {title}
{body}"""


def gemini_extract(rec, key, model, counter, lock):
    ident = "ai_" + hashlib.sha1((rec["url"] + rec["title"]).encode("utf-8")).hexdigest()[:16]
    cached = cache_get(ident, None)
    if cached is not None:
        return cached
    with lock:
        if counter["calls"] >= CONFIG["gemini_max_calls"]:
            return None
        counter["calls"] += 1
    prompt = GEMINI_PROMPT.format(title=rec["title"], body=rec["text"][:CONFIG["gemini_body_chars"]])
    payload = {
        "contents": [{"parts": [{"text": prompt}]}],
        "generationConfig": {"responseMimeType": "application/json", "temperature": 0.2},
    }
    try:
        data = http_post_json_retry(GEMINI_URL.format(model=model, key=key), payload)
        obj = json.loads(data["candidates"][0]["content"]["parts"][0]["text"])
    except Exception as exc:  # noqa: BLE001
        with lock:
            counter["calls"] -= 1
        print(f"[warn] gemini: {exc}")
        return None
    cache_put(ident, obj)
    return obj


def median_budget(budgets):
    if not budgets:
        return None
    lows = [b["min"] for b in budgets]
    highs = [b["max"] for b in budgets]
    period = Counter(b["period"] for b in budgets).most_common(1)[0][0]
    return {"min": statistics.median(lows), "max": statistics.median(highs), "period": period}


def fmt_budget(b):
    if not b:
        return "-"
    unit = {"hourly": "/hr", "monthly": "/mo", "fixed": ""}[b["period"]]
    if abs(b["max"] - b["min"]) < 1:
        return f"${b['min']:,.0f}{unit}"
    return f"${b['min']:,.0f}-{b['max']:,.0f}{unit}"


def new_group():
    return {"demanda": 0, "money": 0, "engagement": 0, "recent": 0,
            "budgets": [], "modalidades": Counter(), "examples": []}


def build_projects(records, use_ai, key, model):
    for rec in records:
        rec["intent"] = classify(rec)
        rec["budget"] = parse_budget(rec["title"] + " " + rec["text"]) if rec["intent"] != "TENDENCIA" else None

    demands = [r for r in records if r["intent"] == "DEMANDA"]
    offers = [r for r in records if r["intent"] == "OFERTA"]
    trends = [r for r in records if r["intent"] == "TENDENCIA"]

    ai_counter = {"calls": 0}
    if use_ai and key:
        lock = threading.Lock()
        demands.sort(key=lambda r: -(r["upvotes"] + r["comments"] + (1000 if r["budget"] else 0)))
        def worker(rec):
            rec["ai"] = gemini_extract(rec, key, model, ai_counter, lock)
        with ThreadPoolExecutor(max_workers=CONFIG["gemini_workers"]) as pool:
            list(pool.map(worker, demands))
        print(f"[gemini] {ai_counter['calls']} llamadas nuevas ({len(demands)} demandas)")

    now = time.time()
    cutoff = now - CONFIG["recency_days"] * 86400

    comp = Counter()
    for rec in offers:
        for ptype in detect_types(rec):
            comp[ptype] += 1

    groups: dict = defaultdict(new_group)
    for rec in demands:
        ai = rec.get("ai")
        types = [ai["tipo"]] if ai and ai.get("tipo") else detect_types(rec)
        budget = rec["budget"]
        if ai and ai.get("presupuesto_min"):
            budget = {"min": ai["presupuesto_min"], "max": ai.get("presupuesto_max") or ai["presupuesto_min"],
                      "period": ai.get("periodo") or "fixed"}
        recent = rec["created"] >= cutoff
        for ptype in types:
            grp = groups[ptype]
            grp["demanda"] += 1
            grp["engagement"] += rec["upvotes"] + rec["comments"]
            grp["recent"] += int(recent)
            if budget:
                grp["money"] += 1
                grp["budgets"].append(budget)
            if ai and ai.get("modalidad"):
                grp["modalidades"][ai["modalidad"]] += 1
            grp["examples"].append(rec)

    rows = []
    for ptype, grp in groups.items():
        ratio = grp["money"] / grp["demanda"]
        recency = grp["recent"] / grp["demanda"]
        base = grp["demanda"] * (1 + CONFIG["weights"]["budget"] * ratio) \
            * (1 - CONFIG["weights"]["recency"] + CONFIG["weights"]["recency"] * recency)
        competencia = comp.get(ptype, 0)
        rows.append({
            "tipo": ptype,
            "demanda": grp["demanda"],
            "money": grp["money"],
            "ratio": ratio,
            "competencia": competencia,
            "engagement": grp["engagement"],
            "recencia": recency,
            "demanda_score": base,
            "oportunidad": base / (1 + competencia),
            "budget": median_budget(grp["budgets"]),
            "modalidades": grp["modalidades"],
            "examples": sorted(grp["examples"],
                               key=lambda r: -(r["upvotes"] + r["comments"]))[:4],
        })
    rows.sort(key=lambda r: -r["oportunidad"])
    assign_buckets(rows)
    return rows, demands, offers, trends


def assign_buckets(rows):
    scores = sorted(row["oportunidad"] for row in rows)
    if not scores:
        return
    def pct(p):
        return scores[min(len(scores) - 1, int(round(p * (len(scores) - 1))))]
    p75, p25 = pct(0.75), pct(0.25)
    for row in rows:
        row["bucket"] = "HOT" if row["oportunidad"] >= p75 else ("COLD" if row["oportunidad"] <= p25 else "WARM")


# -------------------------------------------------------------------- fuentes

def fetch_reddit(refresh, budget):
    key = os.environ.get("REDDITAPIS_KEY")
    if not key:
        print("[warn] REDDITAPIS_KEY ausente: omito Reddit")
        return []
    out, calls = [], 0
    for sub in CONFIG["subreddits"]:
        name = f"reddit_{sub}"
        data = cache_get(name, CONFIG["ttl_hours"]) if not refresh else None
        if data is None:
            if calls >= budget:
                print(f"[reddit] tope de {budget} llamadas, omito r/{sub}")
                break
            url = ("https://api.redditapis.com/api/reddit/posts?"
                   f"subreddit={urllib.parse.quote(sub)}&sort=top&t=month&limit=100")
            data = cached_fetch(name, url, refresh, {"Authorization": f"Bearer {key}"})
            calls += 1
        for post in (data.get("posts") if isinstance(data, dict) else None) or []:
            out.append(norm("reddit", post.get("title", ""),
                            post.get("text") or post.get("selftext") or "",
                            post.get("url") or post.get("permalink", ""),
                            up=post.get("upvotes", 0), com=post.get("comments", 0),
                            created=post.get("created_utc", 0)))
    print(f"[reddit] {len(out)} items ({calls} llamadas nuevas)")
    return out


def hn_thread_story(title, refresh):
    url = ("https://hn.algolia.com/api/v1/search_by_date?tags=story,author_whoishiring"
           "&hitsPerPage=30&query=" + urllib.parse.quote(title))
    data = cached_fetch("hn_story_" + slug(title), url, refresh)
    hits = [h for h in data.get("hits", []) if title.lower() in (h.get("title") or "").lower()]
    hits.sort(key=lambda h: h.get("created_at_i", 0), reverse=True)
    return hits[0] if hits else None


def fetch_hn(refresh):
    out = []
    for thread in CONFIG["hn_threads"]:
        story = hn_thread_story(thread, refresh)
        if not story:
            continue
        sid = story.get("objectID")
        url = f"https://hn.algolia.com/api/v1/search?tags=comment,story_{sid}&hitsPerPage=200"
        data = cached_fetch(f"hn_thread_{sid}", url, refresh)
        for hit in data.get("hits", []):
            out.append(norm("hn", thread, hit.get("comment_text") or "",
                            f"https://news.ycombinator.com/item?id={hit.get('objectID')}",
                            created=hit.get("created_at_i", 0)))
    for query in CONFIG["hn_queries"]:
        url = ("https://hn.algolia.com/api/v1/search?tags=comment&hitsPerPage=50&query="
               + urllib.parse.quote(query))
        data = cached_fetch("hn_" + slug(query), url, refresh)
        for hit in data.get("hits", []):
            out.append(norm("hn", hit.get("story_title") or "", hit.get("comment_text") or "",
                            f"https://news.ycombinator.com/item?id={hit.get('objectID')}",
                            created=hit.get("created_at_i", 0)))
    print(f"[hn] {len(out)} items")
    return out


def fetch_devto(refresh):
    out = []
    for tag in CONFIG["devto_tags"]:
        data = cached_fetch(f"devto_{tag}", f"https://dev.to/api/articles?tag={tag}&per_page=50", refresh)
        for art in data if isinstance(data, list) else []:
            out.append(norm("devto", art.get("title", ""), art.get("description", ""),
                            art.get("url", ""), up=art.get("positive_reactions_count", 0),
                            com=art.get("comments_count", 0), created=to_epoch(art.get("published_at"))))
    print(f"[devto] {len(out)} items")
    return out


def fetch_remoteok(refresh):
    out = []
    data = cached_fetch("remoteok", "https://remoteok.com/api", refresh)
    for job in data if isinstance(data, list) else []:
        if not isinstance(job, dict) or "position" not in job:
            continue
        salary = job.get("salary_min") or 0
        text = (job.get("description") or "") + " " + " ".join(job.get("tags") or [])
        if salary:
            text += f" ${salary}"
        title = f"{job.get('position', '')} @ {job.get('company', '')}"
        out.append(norm("remoteok", title, text, job.get("url") or "", created=job.get("epoch", 0)))
    print(f"[remoteok] {len(out)} items")
    return out


def fetch_github(refresh):
    since = (datetime.now(timezone.utc) - timedelta(days=CONFIG["github_days"])).strftime("%Y-%m-%d")
    query = f"created:>{since} stars:>{CONFIG['github_min_stars']}"
    url = ("https://api.github.com/search/repositories?sort=stars&order=desc&per_page=50&q="
           + urllib.parse.quote(query))
    data = cached_fetch("github", url, refresh, {"Accept": "application/vnd.github+json"})
    out = []
    for repo in data.get("items", []) if isinstance(data, dict) else []:
        text = " ".join(filter(None, [repo.get("description") or "", repo.get("language") or "",
                                      " ".join(repo.get("topics") or [])]))
        out.append(norm("github", repo.get("full_name", ""), text, repo.get("html_url", ""),
                        up=repo.get("stargazers_count", 0), created=to_epoch(repo.get("created_at"))))
    print(f"[github] {len(out)} items")
    return out


def fetch_all(refresh, budget):
    records = []
    for fetch in (lambda: fetch_reddit(refresh, budget), lambda: fetch_hn(refresh),
                  lambda: fetch_devto(refresh), lambda: fetch_remoteok(refresh),
                  lambda: fetch_github(refresh)):
        try:
            records += fetch()
        except Exception as exc:  # noqa: BLE001
            print(f"[warn] fuente fallida: {exc}")
    return records


# --------------------------------------------------------------------- salida

BUCKET_ICON = {"HOT": "##", "WARM": "==", "COLD": "--"}


def print_table(rows, demands, offers, trends, top):
    print(f"\n{'=' * 82}")
    print(f"  CAZADOR DE DEMANDA  |  {len(demands)} demandas / {len(offers)} ofertas / "
          f"{len(trends)} tendencias  |  {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print(f"{'=' * 82}")
    if not rows:
        print("  Sin demanda detectada. Revisa la key o corre con --refresh.")
        return
    print(f"  {'TIPO':<20} {'TEMP':<6} {'DEM':>4} {'$%':>5} {'COMP':>5} {'BUDGET':>16} {'OPORT':>8}")
    print(f"  {'-' * 78}")
    for row in rows[:top]:
        print(f"  {row['tipo']:<20} {BUCKET_ICON[row['bucket']]:<6} {row['demanda']:>4} "
              f"{row['ratio']:>4.0%} {row['competencia']:>5} {fmt_budget(row['budget']):>16} "
              f"{row['oportunidad']:>8.2f}")
    print(f"\n  Formula: oportunidad = demanda_score / (1 + competencia)  (demanda_score = "
          f"demandas * (1+{CONFIG['weights']['budget']}*ratio$) * recencia)")
    print("  Menos competencia = mejor. Ordena por OPORT, no solo por demanda.")


def write_dashboard(rows, demands, offers, trends, path, use_ai):
    hottest = max((r["oportunidad"] for r in rows), default=1.0) or 1.0
    peak_demand = max((r["demanda_score"] for r in rows), default=1.0) or 1.0
    colors = {"HOT": "#ff5d5d", "WARM": "#ffb454", "COLD": "#5aa9e6"}

    opp_bars = []
    for row in rows:
        width = max(3.0, row["oportunidad"] / hottest * 100)
        opp_bars.append(
            f'<div class="row"><div class="kw">{row["tipo"]}</div>'
            f'<div class="bar"><span style="width:{width:.1f}%;background:{colors[row["bucket"]]}"></span></div>'
            f'<div class="val">{row["oportunidad"]:.1f}</div>'
            f'<div class="meta">{row["bucket"]} · demanda {row["demanda"]} · $ {row["ratio"]:.0%} · '
            f'comp {row["competencia"]} · {fmt_budget(row["budget"])}</div></div>')

    dem_bars = []
    for row in sorted(rows, key=lambda r: -r["demanda_score"])[:15]:
        width = max(3.0, row["demanda_score"] / peak_demand * 100)
        dem_bars.append(
            f'<div class="row"><div class="kw">{row["tipo"]}</div>'
            f'<div class="bar"><span style="width:{width:.1f}%;background:#7c8cff"></span></div>'
            f'<div class="val">{row["demanda_score"]:.1f}</div>'
            f'<div class="meta">{row["demanda"]} posts · {fmt_budget(row["budget"])}</div></div>')

    offer_rows = []
    for row in rows:
        for ex in row["examples"][:2]:
            budget = fmt_budget(ex["budget"])
            title = html_mod.escape(ex["title"][:110]) or "(sin titulo)"
            offer_rows.append(
                f'<li><a href="{html_mod.escape(ex["url"])}" target="_blank">{title}</a> '
                f'<span class="tag">{row["tipo"]}</span> <span class="money">{budget}</span> '
                f'<span class="src">{ex["source"]}</span></li>')

    comp_rows = "".join(
        f'<tr><td>{ptype}</td><td>{count}</td></tr>'
        for ptype, count in sorted({r["tipo"]: r["competencia"] for r in rows}.items(),
                                   key=lambda kv: -kv[1]))

    trend_kw = Counter()
    for rec in trends:
        blob = (rec["title"] + " " + rec["text"]).lower()
        for ptype, triggers in TAXONOMY.items():
            if any(t in blob for t in triggers):
                trend_kw[ptype] += 1
    trend_rows = "".join(f'<tr><td>{k}</td><td>{v}</td></tr>' for k, v in trend_kw.most_common(15))

    ai_tag = "con IA (Gemini)" if use_ai else "sin IA (regex)"
    html = f"""<!doctype html><html lang="es"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Cazador de Demanda</title><style>
:root{{color-scheme:dark}}*{{box-sizing:border-box}}
body{{margin:0;background:#0e1116;color:#e6edf3;font:14px/1.5 "Segoe UI",system-ui,sans-serif;padding:32px}}
h1{{font-size:22px;margin:0 0 4px}}h2{{font-size:14px;margin:34px 0 12px;color:#9aa7b4;text-transform:uppercase;letter-spacing:.08em}}
.sub{{color:#7d8794;margin-bottom:14px}}
.row{{display:grid;grid-template-columns:170px 1fr 60px 320px;gap:12px;align-items:center;padding:6px 0;border-bottom:1px solid #1b2129}}
.kw{{font-weight:600}}.bar{{background:#161b22;border-radius:4px;height:18px;overflow:hidden}}
.bar span{{display:block;height:100%;border-radius:4px}}.val{{text-align:right;font-variant-numeric:tabular-nums}}
.meta{{color:#8b96a3;font-size:12px}}
ul.of{{list-style:none;padding:0;margin:0}}ul.of li{{padding:7px 0;border-bottom:1px solid #1b2129}}
a{{color:#7cc4ff;text-decoration:none}}a:hover{{text-decoration:underline}}
.tag{{background:#1e2630;border-radius:4px;padding:1px 7px;font-size:11px;color:#9fb2c4}}
.money{{color:#7ee787;font-size:12px}}.src{{color:#6b7683;font-size:11px}}
table{{border-collapse:collapse;width:100%;max-width:520px}}
th,td{{text-align:left;padding:5px 10px;border-bottom:1px solid #1b2129}}th{{color:#9aa7b4}}
footer{{margin-top:34px;color:#6b7683;font-size:12px}}
</style></head><body>
<h1>Cazador de Demanda</h1>
<div class="sub">{len(demands)} demandas · {len(offers)} ofertas · {len(trends)} tendencias · extraccion {ai_tag} · {datetime.now().strftime('%Y-%m-%d %H:%M')}</div>

<h2>Oportunidad (demanda vs competencia)</h2>
{''.join(opp_bars) or '<p>Sin datos.</p>'}

<h2>Mas demandados</h2>
{''.join(dem_bars) or '<p>Sin datos.</p>'}

<h2>Ofertas concretas (compradores buscando)</h2>
<ul class="of">{''.join(offer_rows) or '<li>Sin datos.</li>'}</ul>

<h2>Competencia (ofertas de freelancers por tipo)</h2>
<table><tr><th>Tipo</th><th>Ofertas</th></tr>{comp_rows or '<tr><td colspan="2">-</td></tr>'}</table>

<h2>Tendencias tecnicas</h2>
<table><tr><th>Tema</th><th>Menciones</th></tr>{trend_rows or '<tr><td colspan="2">-</td></tr>'}</table>

<footer>Heuristico. "Oportunidad" = demanda x presupuesto x recencia / competencia. No es profit real.</footer>
</body></html>"""
    path.write_text(html, encoding="utf-8")


# ------------------------------------------------------------------- offline

def sample_records():
    return [
        norm("reddit", "[Hiring] React/Node dashboard ($3,000/month)",
             "Need a full-stack developer for a SaaS dashboard with API integration. $3,000/month.",
             "https://r/1", up=120, com=60, created=int(time.time())),
        norm("reddit", "[Hiring] Chrome extension + web scraping ($25/hr)",
             "Looking for someone to build a chrome extension and web scraping automation. Pay $25/hour.",
             "https://r/2", up=80, com=30, created=int(time.time())),
        norm("reddit", "[For Hire] I build web scrapers",
             "I build web scrapers and automation in python, $20/hr.", "https://r/3", up=10, com=2),
        norm("reddit", "[For Hire] Automation expert available",
             "I develop automation and scraping tools.", "https://r/4", up=5, com=1),
        norm("hn", "Freelancer? Seeking freelancer?", "SEEKING FREELANCER | remote | need an AI chatbot with RAG, budget $8000.",
             "https://hn/1", created=int(time.time())),
        norm("devto", "Why React and Nextjs still win", "react typescript nextjs", "https://dev/1", up=200, com=15),
        norm("github", "awesome/python-automation", "python automation scraper bots", "https://gh/1", up=900),
    ]


def demo():
    assert classify(norm("reddit", "[Hiring] dev", "", "u")) == "DEMANDA"
    assert classify(norm("reddit", "[For Hire] me", "", "u")) == "OFERTA"
    assert classify(norm("devto", "hard issue", "", "u")) == "TENDENCIA"

    b = parse_budget("React dev $35-$50/hr")
    assert b and b["min"] == 35 and b["max"] == 50 and b["period"] == "hourly", b
    b = parse_budget("salary $2,000-3,000/month")
    assert b and b["period"] == "monthly" and b["min"] == 2000 and b["max"] == 3000, b
    b = parse_budget("budget $8000")
    assert b and b["min"] == 8000 and b["period"] == "fixed", b

    assert "web scraper" in detect_types(norm("reddit", "web scraping automation", "", "u"))

    rows, demands, offers, trends = build_projects(sample_records(), False, None, None)
    assert rows and demands and offers, "debe haber demanda y oferta"
    scan = next(r for r in rows if r["tipo"] == "web scraper")
    assert scan["competencia"] >= 1, "debe contar competencia de las ofertas"
    assert any(r["bucket"] == "HOT" for r in rows), "debe haber al menos un HOT"
    print("[self-test] OK")


# ---------------------------------------------------------------------- main

def main():
    parser = argparse.ArgumentParser(description="Cazador de demanda de proyectos.")
    parser.add_argument("--refresh", action="store_true", help="ignora la cache")
    parser.add_argument("--offline", action="store_true", help="autotest + datos de muestra")
    parser.add_argument("--ai", action="store_true", help="extraccion con Gemini (GEMINI_API_KEY)")
    parser.add_argument("--budget", type=int, default=CONFIG["max_reddit_calls"], help="tope de llamadas Reddit")
    parser.add_argument("--ai-max", type=int, default=CONFIG["gemini_max_calls"], help="tope de llamadas Gemini")
    parser.add_argument("--workers", type=int, default=CONFIG["gemini_workers"], help="llamadas Gemini en paralelo")
    parser.add_argument("--top", type=int, default=20, help="filas en la tabla")
    args = parser.parse_args()

    load_env()
    CONFIG["gemini_max_calls"] = args.ai_max
    CONFIG["gemini_workers"] = max(1, args.workers)

    if args.offline:
        demo()
        records = sample_records()
    else:
        records = fetch_all(refresh=args.refresh, budget=args.budget)

    key = os.environ.get("GEMINI_API_KEY")
    model = os.environ.get("GEMINI_MODEL", CONFIG["gemini_model"])
    use_ai = args.ai and bool(key)
    if args.ai and not key:
        print("[warn] --ai sin GEMINI_API_KEY: sigo sin IA")

    rows, demands, offers, trends = build_projects(records, use_ai, key, model)
    print_table(rows, demands, offers, trends, args.top)
    write_dashboard(rows, demands, offers, trends, DASHBOARD, use_ai)
    print(f"\n  Dashboard: {DASHBOARD}")


if __name__ == "__main__":
    main()
