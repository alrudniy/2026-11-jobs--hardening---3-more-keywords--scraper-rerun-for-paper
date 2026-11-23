#!/usr/bin/env python3
"""
scraper_v2.py - Google job search scraper, second version (November 2026).

What changed from scraper.py (February 2025)
  1. Queries are read from queries.json. The default file holds only the three 2025 search strings
     (one per area), so the second wave repeats the same keyword search. More queries can be added.
  2. Every result is logged (hits.csv), and each distinct listing is saved once (listings.jsonl),
     so the data reduction can be reported: results seen per query -> distinct listings.
  3. Each listing gets a stable ID: Google's own listing ID (data-encoded-docid) when present,
     otherwise a hash of title, employer, and location. Saved files are named with that ID,
     so listings with the same employer and title no longer overwrite each other.
  4. The details pane is matched by its data-title and listing ID, not by "title appears in the
     aria-label", which could pick the pane of a neighboring result with a similar title.
  5. All "Apply on ..." links are saved (platform name and URL), plus the share URL of the listing.
     Google often groups several platforms under one listing; the old script kept only "via X".
  6. Optional: open the employer or applicant-tracking page behind an apply link and save its text
     (--follow-apply). Aggregator pages are never opened. A listing that exists only on an
     aggregator stays short; it is flagged (aggregator_only) so results can be reported both ways.
  7. Bug fix: the Responsibilities field used to be a copy of Benefits.
  8. A screening flag per listing from the include and exclude terms in queries.json
     (nothing is deleted; the flag is a starting point for manual review).
  9. Output workbook keeps the nine original columns (Title, Company, Location, Timestamp,
     Job Highlights, Qualifications, Benefits, Responsibilities, Job Description) so the extraction
     script runs unchanged, and adds the new fields after them.

The field definitions (highlights, qualifications, description) use the same page elements as the
first version so that the two waves are comparable.

IMPORTANT: the page selectors below are the ones that worked in February 2025. Google changes its
markup without notice. Run the self-test first:
    python scraper_v2.py --area radiation_hardening --check
It runs the first query, processes three listings, and reports which selectors matched.

Usage
    python scraper_v2.py --area radiation_hardening
    python scraper_v2.py --area compound_semiconductors --follow-apply
    python scraper_v2.py --area system_on_chip --follow-apply
    python scraper_v2.py --area system_on_chip --only-query "system on chip jobs"
    python scraper_v2.py --area radiation_hardening --run-id 20261120_090000     (resume that run)

Requires: selenium (4.6 or later), pandas, openpyxl. Chrome must be installed.
"""
import argparse
import csv
import hashlib
import json
import os
import random
import re
import sys
import time
from datetime import datetime
from urllib.parse import quote, quote_plus, urlparse, urlunparse, parse_qs, parse_qsl, urlencode, unquote

from selenium import webdriver
from selenium.common.exceptions import WebDriverException
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys

VERSION = "2.0 (2026-11-19)"

# --------------------------------------------------------------------------- selectors (February 2025 markup)
SEL = {
    "search_box_name": "q",
    "jobs_tab_link_text": "Jobs",
    "item_title": ".tNxQIb.PUpOsf",                      # job title inside a result card
    "item_container_xpath": "./ancestor::div[@role='button' or @jsslot][1]",   # the clickable card around a title (Google dropped jsslot ~Nov 2026; role=button div holds title/company/location)
    "item_company": ".wHYlTd.MKCbgd.a3jPc",
    "item_location": ".wHYlTd.FqK3wc.MKCbgd",            # "City, ST • via Platform"
    "details_pane": "c-wiz[aria-label^='Job details for'], div[aria-label^='Job details for']",   # div since ~Nov 2026
    "apply_links": "a[href*='google_jobs_apply']",
    "apply_buttons": "a[title^='Apply on '], a[title^='Apply directly on ']",   # since ~Nov 2026 (href is an encrypted /goto link)
    "share_url_attr": "data-share-url",
}
EXPANDERS = ["More job highlights", "Show full description"]
JOBS_URL = "https://www.google.com/search?q={q}&udm=8&hl=en&gl=us"   # udm=8 is the Jobs view

# Platforms that republish postings. Their pages are never fetched by --follow-apply.
AGGREGATOR_DOMAINS = (
    "bebee.", "tealhq.", "linkedin.", "indeed.", "ziprecruiter.", "glassdoor.", "jobilize.", "trabajo.org",
    "trawle.", "searchremotely.", "talent.com", "jooble.", "simplyhired.", "monster.", "careerbuilder.",
    "theladders.", "jobzmall.", "lensa.", "whatjobs.", "adzuna.", "jobrapido.", "recruit.net", "experteer.",
    "learn4good.", "salary.com", "snagajob.", "dice.com", "builtin.", "wellfound.", "simplify.jobs", "joblist.",
    "grabjobs.", "jobleads.", "talentify.", "womeninscience.", "stemcareers.", "academicwomen.", "diversityjobs.",
    "recruitmilitary.", "clearancejobs.", "securityclearancejobs.", "clearedjobs.", "jobs2careers.", "nexxt.",
    "careerjet.", "jobget.", "upwork.", "vaia.", "thebigjobs.", "disabilitysolutions.", "getwork.", "jobtarget.",
    "ihiretechnology.", "hercjobs.", "higheredjobs.", "sercanto.", "jobsora.", "expertini.", "tallo.", "ripplematch.",
    "handshake.", "wayup.", "energyjobline.", "nuclearstreet.", "spacecrew.", "spaceindividuals.", "startup.jobs",
)


def now_iso():
    return datetime.now().isoformat(timespec="seconds")


def pause(a=1.0, b=2.0):
    time.sleep(random.uniform(a, b))


def slug(text, n=60):
    return re.sub(r"_+", "_", "".join(c if c.isalnum() else "_" for c in str(text))).strip("_")[:n]


def norm(text):
    return re.sub(r"\s+", " ", str(text or "")).strip().lower()


def pre_key(title, company, location):
    """ID available before the listing is opened."""
    return hashlib.sha1("|".join(norm(x) for x in (title, company, location)).encode("utf-8")).hexdigest()[:12]


def split_location(location):
    """'City, ST • via Platform' -> ('City, ST', 'Platform')."""
    loc = str(location or "")
    place = loc.split("•")[0].strip()
    via = loc.split("via", 1)[1].strip() if "via" in loc else ""
    return place, via


def clean_apply_url(url):
    """Drop the utm_* tracking parameters that Google adds to an apply link."""
    try:
        u = urlparse(url or "")
        keep = [(k, v) for k, v in parse_qsl(u.query, keep_blank_values=True) if not k.lower().startswith("utm_")]
        return urlunparse(u._replace(query=urlencode(keep)))
    except Exception:
        return url or ""


def is_aggregator(url):
    host = urlparse(url or "").netloc.lower()
    return any(d in host for d in AGGREGATOR_DOMAINS)


def docid_from_share_url(url):
    try:
        v = parse_qs(urlparse(url).query).get("htidocid", [""])[0]
        return unquote(v)
    except Exception:
        return ""


def screen(text, title, rules):
    """Return (flag, include_hits, exclude_hits). Flag is 'keep' or 'review'. Nothing is deleted."""
    hay = f"{title}\n{text}"
    inc = [t for t in rules.get("include_terms_case_sensitive", []) if re.search(t, hay)]
    inc += [t for t in rules.get("include_terms", []) if re.search(t, hay, flags=re.I)]
    exc = [t for t in rules.get("exclude_terms", []) if re.search(t, hay, flags=re.I)]
    return ("keep" if inc and not exc else "review"), inc, exc


# --------------------------------------------------------------------------- page functions
def js_click(driver, el):
    driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", el)
    try:
        el.click()
    except WebDriverException:
        driver.execute_script("arguments[0].click();", el)


def blocked(driver):
    url = driver.current_url
    return "/sorry/" in url or "unusual traffic" in driver.page_source[:20000].lower()


def open_jobs_view(driver, query):
    """Open the Jobs view for a query. Falls back to typing the query and clicking the Jobs tab."""
    driver.get(JOBS_URL.format(q=quote_plus(query)))
    pause(2.0, 3.0)
    if blocked(driver):
        input("Google is asking for verification. Solve it in the browser, then press Enter here...")
    if driver.find_elements(By.CSS_SELECTOR, SEL["item_title"]):
        return "direct_url"
    try:                                               # original route
        driver.get("https://www.google.com/?hl=en&gl=us")
        pause(1.5, 2.5)
        box = driver.find_element(By.NAME, SEL["search_box_name"])
        box.clear(); box.send_keys(query); box.send_keys(Keys.RETURN)
        pause(2.0, 3.0)
        driver.find_element(By.LINK_TEXT, SEL["jobs_tab_link_text"]).click()
        pause(2.0, 3.0)
        return "jobs_tab"
    except WebDriverException as e:
        print(f"  could not open the Jobs view: {str(e)[:120]}")
        return "failed"


def load_all_results(driver, max_rounds=80, pause_s=2.0):
    """Scroll until no more results load (same approach as the first version)."""
    last = driver.execute_script("return document.body.scrollHeight")
    for _ in range(max_rounds):
        driver.execute_script("window.scrollTo(0, document.body.scrollHeight);")
        time.sleep(pause_s)
        new = driver.execute_script("return document.body.scrollHeight")
        if new == last:
            break
        last = new
    driver.execute_script("window.scrollTo(0, 0);")
    time.sleep(1.0)


def list_items(driver, tries=3):
    """One entry per result card: (container element, title, company, location).
    Retries if some cards could not be read, so a slow page does not silently shorten the list."""
    best = []
    for _ in range(tries):
        titles = driver.find_elements(By.CSS_SELECTOR, SEL["item_title"])
        out = []
        for t in titles:
            try:
                box = t.find_element(By.XPATH, SEL["item_container_xpath"])
                title = (t.text or t.get_attribute("textContent") or "").strip()

                def txt(css):
                    els = box.find_elements(By.CSS_SELECTOR, css)
                    return (els[0].text or els[0].get_attribute("textContent") or "").strip() if els else ""

                if title:
                    out.append((box, title, txt(SEL["item_company"]), txt(SEL["item_location"])))
            except WebDriverException:
                continue
        if len(out) > len(best):
            best = out
        if len(out) == len(titles):
            break
        time.sleep(1.5)
    return best


def share_urls(driver):
    """Share URLs of all results on the page, in result order. Each carries the listing ID (htidocid)."""
    out = []
    for el in driver.find_elements(By.CSS_SELECTOR, f"[{SEL['share_url_attr']}]"):
        u = el.get_attribute(SEL["share_url_attr"]) or ""
        out.append((docid_from_share_url(u), u))
    return out


def find_pane(driver, title, used_docids, expected_index=None, timeout=8.0):
    """Details pane for the listing just opened. Google keeps the panes of neighboring results in the
    page, so the pane must match the title exactly and must not belong to a listing already saved.
    Preference: the pane whose data-result-index equals the position of the card (0-based)."""
    end = time.time() + timeout
    while time.time() < end:
        exact_pos, fresh, any_match = [], [], []
        for p in driver.find_elements(By.CSS_SELECTOR, SEL["details_pane"]):
            try:
                dt = (p.get_attribute("data-title") or "").strip()
                label = (p.get_attribute("aria-label") or "")
                docid = p.get_attribute("data-encoded-docid") or ""
                if not (dt == title or label == f"Job details for {title}" or ((not dt) and title in label)):
                    continue
                idx = p.get_attribute("data-result-index")
                i = int(idx) if (idx or "").isdigit() else 10**6
                key = (0 if p.is_displayed() else 1, i)
                any_match.append((key, p))
                if expected_index is not None and i == expected_index:
                    exact_pos.append((key, p))
                if not docid or docid not in used_docids:
                    fresh.append((key, p))
            except WebDriverException:
                continue
        # 1. the pane at the card's own position; 2. a matching pane not saved before; 3. any matching pane
        for group in (exact_pos, fresh, any_match):
            if group:
                group.sort(key=lambda c: c[0])
                return group[0][1], len(any_match)
        time.sleep(0.4)
    return None, 0


def expand(driver, pane):
    """Click 'More job highlights' and 'Show full description' inside the pane, if present."""
    for label in EXPANDERS:
        try:
            for el in pane.find_elements(By.XPATH, f".//*[normalize-space(text())='{label}']"):
                js_click(driver, el)
                pause(0.8, 1.4)
        except WebDriverException:
            pass


def ul_after(pane, xpath):
    """Text and list items of the first <ul> matched by xpath, or ('', [])."""
    els = pane.find_elements(By.XPATH, xpath)
    if not els:
        return "", []
    ul = els[0]
    items = [(li.text or li.get_attribute("textContent") or "").strip() for li in ul.find_elements(By.TAG_NAME, "li")]
    return (ul.text or ul.get_attribute("textContent") or "").strip(), [i for i in items if i]


def posting_urls(pane):
    """Posting URLs from the pane's data-maindata JSON: the values of jobs_posting_urls_1, _2, ... in order."""
    found = {}

    def walk(x):
        if isinstance(x, list):
            if len(x) == 2 and isinstance(x[0], str) and isinstance(x[1], str):
                m = re.fullmatch(r"jobs_posting_urls_(\d+)", x[0])
                if m:
                    found[int(m.group(1))] = x[1].strip()
                    return
            for y in x:
                walk(y)
        elif isinstance(x, dict):
            for y in x.values():
                walk(y)

    for el in pane.find_elements(By.CSS_SELECTOR, "[data-maindata]"):
        try:
            walk(json.loads(el.get_attribute("data-maindata") or "null"))
        except (ValueError, WebDriverException):
            continue
        if found:
            break
    return [found[k] for k in sorted(found)]


def extract(pane):
    """Fields of one listing. Same page elements as the first version of the scraper."""
    H = ".//h3[text()='Job highlights']"
    rec = {}
    # Since ~Nov 2026 the h4 + ul blocks sit inside a div after the h3; the direct-sibling form is the older layout.
    rec["job_highlights_text"], rec["job_highlights_items"] = ul_after(pane, f"({H}/following-sibling::ul | {H}/following-sibling::*//ul)")
    for key, head in (("qualifications", "Qualifications"), ("benefits", "Benefits"), ("responsibilities", "Responsibilities")):
        rec[f"{key}_text"], rec[f"{key}_items"] = ul_after(
            pane, f"({H}/following-sibling::h4[text()='{head}']/following-sibling::ul | "
                  f"{H}/following-sibling::*//h4[text()='{head}']/following-sibling::ul)")
    parts, hidden_used = [], False
    for sp in pane.find_elements(By.XPATH, ".//*[self::h2 or self::h3][text()='Job description']/following-sibling::span"):
        t = (sp.text or "").strip()                      # visible text, as in version 1
        if not t:                                        # still collapsed: take the hidden remainder, skip the "..." marker
            tc = (sp.get_attribute("textContent") or "").strip()
            if len(tc.split()) >= 5:
                t, hidden_used = tc, True
        if t:
            parts.append(t)
    rec["job_description"] = "\n".join(parts) + ("\n" if parts else "")
    rec["description_from_hidden_text"] = hidden_used
    links, seen = [], set()
    anchors = pane.find_elements(By.CSS_SELECTOR, SEL["apply_links"])
    if anchors:                                          # older layout: the posting URL is the anchor's href
        pairs = [(a, a.get_attribute("href")) for a in anchors]
    else:                                                # since ~Nov 2026: href is an encrypted /goto link; the posting
        posting = posting_urls(pane)                     # URLs sit in data-maindata, in the same order as the buttons
        anchors = pane.find_elements(By.CSS_SELECTOR, SEL["apply_buttons"])
        pairs = [(a, posting[i] if i < len(posting) else "") for i, a in enumerate(anchors)]
        if len(posting) != len(anchors):
            rec["apply_links_count_mismatch"] = f"{len(anchors)} buttons, {len(posting)} URLs"
    for a, href in pairs:
        url = clean_apply_url(href)
        label = (a.get_attribute("title") or a.text or a.get_attribute("textContent") or "").strip()
        if url and url not in seen:
            seen.add(url)
            links.append({"label": label, "platform": re.sub(r"^Apply (directly )?on ", "", label), "url": url, "aggregator": is_aggregator(url)})
    rec["apply_links"] = links
    rec["aggregator_only"] = bool(links) and all(l["aggregator"] for l in links)
    rec["docid"] = pane.get_attribute("data-encoded-docid") or ""
    rec["result_index"] = pane.get_attribute("data-result-index") or ""
    return rec


def fetch_employer_page(driver, main_handle, links, out_dir, key):
    """Open the first non-aggregator apply link in a second tab and save its HTML and visible text."""
    target = next((l for l in links if not l["aggregator"]), None)
    if not target:
        return {}
    info = {"employer_page_url_requested": target["url"]}
    try:
        driver.switch_to.new_window("tab")
        driver.set_page_load_timeout(30)
        driver.get(target["url"])
        pause(3.5, 5.0)                                   # applicant-tracking sites render with JavaScript
        text = driver.execute_script("return document.body ? document.body.innerText : '';") or ""
        os.makedirs(out_dir, exist_ok=True)
        with open(os.path.join(out_dir, f"{key}.html"), "w", encoding="utf-8") as f:
            f.write(driver.page_source)
        with open(os.path.join(out_dir, f"{key}.txt"), "w", encoding="utf-8") as f:
            f.write(text)
        info.update({"employer_page_url": driver.current_url, "employer_page_file": f"employer_pages/{key}.txt", "employer_page_words": len(text.split())})
    except WebDriverException as e:
        info["employer_page_error"] = str(e)[:160]
    finally:
        try:
            if driver.current_window_handle != main_handle:
                driver.close()
        except WebDriverException:
            pass
        driver.switch_to.window(main_handle)
    return info


# --------------------------------------------------------------------------- outputs
ORIGINAL_COLS = ["Title", "Company", "Location", "Timestamp", "Job Highlights", "Qualifications", "Benefits", "Responsibilities", "Job Description"]


def write_workbook(run_dir, area, run_id):
    import pandas as pd
    path = os.path.join(run_dir, "listings.jsonl")
    if not os.path.exists(path):
        return None
    rows = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            place, via = split_location(r.get("location"))
            links = r.get("apply_links", [])
            rows.append({
                "Title": r.get("title"), "Company": r.get("company"), "Location": r.get("location"), "Timestamp": r.get("timestamp"),
                "Job Highlights": r.get("job_highlights_text") or None, "Qualifications": r.get("qualifications_text") or None,
                "Benefits": r.get("benefits_text") or None, "Responsibilities": r.get("responsibilities_text") or None,
                "Job Description": r.get("job_description") or None,
                "Area": area, "Wave": run_id, "Listing ID": r.get("listing_id"), "Google Doc ID": r.get("docid"),
                "First Query": r.get("query"), "Query Type": r.get("query_type"), "Rank In Query": r.get("rank"),
                "Place": place, "Via": via, "Platforms": "; ".join(l["platform"] for l in links),
                "Apply URLs": "\n".join(l["url"] for l in links), "Aggregator Only": r.get("aggregator_only"),
                "Share URL": r.get("share_url"), "Description Words": len((r.get("job_description") or "").split()),
                "Employer Page URL": r.get("employer_page_url"), "Employer Page File": r.get("employer_page_file"),
                "Employer Page Words": r.get("employer_page_words"), "Screen (auto)": r.get("screen"),
                "Include Terms Found": "; ".join(r.get("include_hits", [])), "Exclude Terms Found": "; ".join(r.get("exclude_hits", [])),
                "Screen (final)": None, "Pane File": r.get("pane_file"), "Pane Candidates": r.get("pane_candidates"),
            })
    df = pd.DataFrame(rows)
    if len(df):
        df = df[ORIGINAL_COLS + [c for c in df.columns if c not in ORIGINAL_COLS]]   # original nine columns first
    out = os.path.join(run_dir, f"{area}_jobs_{run_id}.xlsx")
    df.to_excel(out, index=False, sheet_name="Job Listings")
    return out


def main():
    ap = argparse.ArgumentParser(description="Google job search scraper, version 2")
    ap.add_argument("--area", required=True, help="key in queries.json, e.g. radiation_hardening")
    ap.add_argument("--queries", default="queries.json")
    ap.add_argument("--only-query", help="run a single query string from the area (or any string)")
    ap.add_argument("--out", default="runs")
    ap.add_argument("--run-id", help="reuse an existing run folder to resume it")
    ap.add_argument("--max-per-query", type=int, default=0, help="stop after this many results per query (0 = all)")
    ap.add_argument("--follow-apply", action="store_true", help="save the employer or applicant-tracking page when one is linked")
    ap.add_argument("--chromedriver", help="path to chromedriver; default lets Selenium find a matching driver")
    ap.add_argument("--check", action="store_true", help="self-test: first query, three listings, report which selectors matched")
    args = ap.parse_args()

    with open(args.queries, encoding="utf-8") as f:
        cfg = json.load(f)
    if args.area not in cfg:
        sys.exit(f"Area '{args.area}' is not in {args.queries}. Available: {[k for k in cfg if not k.startswith('_')]}")
    rules = cfg[args.area]
    queries = rules["queries"]
    if args.only_query:
        queries = [q for q in queries if q["q"] == args.only_query] or [{"q": args.only_query, "type": "adhoc"}]
    if args.check:
        queries = queries[:1]

    run_id = args.run_id or datetime.now().strftime("%Y%m%d_%H%M%S")
    run_dir = os.path.join(args.out, args.area, run_id + ("_check" if args.check else ""))
    os.makedirs(os.path.join(run_dir, "html"), exist_ok=True)
    listings_path, hits_path = os.path.join(run_dir, "listings.jsonl"), os.path.join(run_dir, "hits.csv")

    seen_keys, used_docids, done_queries = set(), set(), set()
    if os.path.exists(listings_path):                      # resume
        with open(listings_path, encoding="utf-8") as f:
            for line in f:
                r = json.loads(line)
                seen_keys.add(r["pre_key"])
                if r.get("docid"):
                    used_docids.add(r["docid"])
    previous_queries = []
    info_path = os.path.join(run_dir, "run_info.json")
    if os.path.exists(info_path):
        with open(info_path, encoding="utf-8") as f:
            previous_queries = json.load(f).get("queries_done", [])
        done_queries = {q["q"] for q in previous_queries if q.get("route") != "failed"}
    if seen_keys or done_queries:
        print(f"Resuming run {run_id}: {len(seen_keys)} listings already saved, {len(done_queries)} queries done.")

    opts = Options()
    opts.add_argument("--start-maximized")
    opts.add_argument("--lang=en-US")
    driver = webdriver.Chrome(service=Service(args.chromedriver), options=opts) if args.chromedriver else webdriver.Chrome(options=opts)
    main_handle = driver.current_window_handle
    info = {"script_version": VERSION, "area": args.area, "run_id": run_id, "started": now_iso(), "follow_apply": args.follow_apply,
            "max_per_query": args.max_per_query, "browser": driver.capabilities.get("browserName"),
            "browser_version": driver.capabilities.get("browserVersion"), "queries_done": list(previous_queries), "selectors": SEL}
    new_file = not os.path.exists(hits_path)
    hits_f = open(hits_path, "a", newline="", encoding="utf-8")
    hits = csv.writer(hits_f)
    if new_file:
        hits.writerow(["area", "query", "query_type", "rank", "pre_key", "listing_id", "status", "title", "company", "location", "timestamp"])

    try:
        for q in queries:
            query, qtype = q["q"], q.get("type", "")
            if query in done_queries:
                print(f"\n=== {query}  (already done in this run, skipped)")
                continue
            print(f"\n=== {query}")
            route = open_jobs_view(driver, query)
            if route == "failed":
                info["queries_done"].append({"q": query, "type": qtype, "route": route, "results": 0, "new": 0, "repeat": 0, "errors": 0})
                continue
            load_all_results(driver)
            items = list_items(driver)
            shares = share_urls(driver)
            aligned = len(shares) == len(items) and all(d for d, _ in shares)   # one share URL per card, same order
            share_by_docid = {d: u for d, u in shares if d}
            qdir = os.path.join(run_dir, "html", slug(query))
            os.makedirs(qdir, exist_ok=True)
            with open(os.path.join(qdir, "results_page.html"), "w", encoding="utf-8") as f:
                f.write(driver.page_source)
            n_cards = len(driver.find_elements(By.CSS_SELECTOR, SEL["item_title"]))
            if len(items) < n_cards:
                print(f"  WARNING: {n_cards} cards on the page but only {len(items)} could be read")
            if args.check:
                print(f"  self-test: cards={n_cards}  share URLs={len(shares)}  share URLs aligned with cards={aligned}  route={route}")
            if args.max_per_query:
                items = items[: args.max_per_query]
            if args.check:
                items = items[:3]
            print(f"  {len(items)} results")
            n_new = n_rep = n_err = 0
            for rank, (box, title, company, location) in enumerate(items, 1):
                pk = pre_key(title, company, location)
                predicted = shares[rank - 1][0] if aligned else ""
                if pk in seen_keys or (predicted and predicted in used_docids):   # already saved under an earlier query
                    hits.writerow([args.area, query, qtype, rank, pk, predicted, "repeat", title, company, location, now_iso()]); n_rep += 1
                    continue
                try:
                    js_click(driver, box)
                    pause(1.5, 2.5)
                    pane, n_cand = find_pane(driver, title, used_docids, expected_index=rank - 1)
                    if pane is None:
                        raise RuntimeError("details pane not found")
                    expand(driver, pane)
                    rec = extract(pane)
                    rec["share_url"] = share_by_docid.get(rec["docid"], "")
                    if not rec["share_url"] and rec["docid"]:
                        rec["share_url"] = f"https://www.google.com/search?ibp=htl;jobs&q={quote_plus(query)}&htidocid={quote(rec['docid'], safe='')}"
                    rec["docid_matches_list_position"] = (rec["docid"] == predicted) if predicted else None
                    listing_id = rec["docid"] or pk
                    if rec["docid"] and rec["docid"] in used_docids:   # same Google listing reached through a different card
                        hits.writerow([args.area, query, qtype, rank, pk, listing_id, "repeat", title, company, location, now_iso()]); n_rep += 1
                        seen_keys.add(pk)
                        continue
                    fid = slug(listing_id, 24)
                    pane_file = os.path.join("html", slug(query), f"{rank:03d}_{slug(company, 30)}_{slug(title, 40)}_{fid}.html")
                    with open(os.path.join(run_dir, pane_file), "w", encoding="utf-8") as f:
                        f.write(pane.get_attribute("outerHTML") or "")
                    flag, inc, exc = screen(rec["job_description"], title, rules)
                    rec.update({"area": args.area, "query": query, "query_type": qtype, "rank": rank, "pre_key": pk, "listing_id": listing_id,
                                "title": title, "company": company, "location": location, "timestamp": now_iso(),
                                "pane_file": pane_file.replace(os.sep, "/"), "pane_candidates": n_cand,
                                "screen": flag, "include_hits": inc, "exclude_hits": exc})
                    if args.follow_apply:
                        rec.update(fetch_employer_page(driver, main_handle, rec["apply_links"], os.path.join(run_dir, "employer_pages"), fid))
                    with open(listings_path, "a", encoding="utf-8") as f:
                        f.write(json.dumps(rec, ensure_ascii=False) + "\n")
                    seen_keys.add(pk)
                    if rec["docid"]:
                        used_docids.add(rec["docid"])
                    hits.writerow([args.area, query, qtype, rank, pk, listing_id, "new", title, company, location, rec["timestamp"]]); n_new += 1
                    words = len(rec["job_description"].split())
                    print(f"  {rank:3d} new  {words:5d} words  {len(rec['apply_links'])} apply links  {title[:50]} | {company[:25]}")
                    if args.check:
                        print(f"        docid={'yes' if rec['docid'] else 'NO'}  highlights={'yes' if rec['job_highlights_text'] else 'no'}  "
                              f"qualifications={'yes' if rec['qualifications_text'] else 'no'}  description={'yes' if words else 'NO'}  "
                              f"share_url={'yes' if rec['share_url'] else 'no'}  pane candidates={n_cand}")
                except Exception as e:                                # keep going; the hit is logged with the error
                    hits.writerow([args.area, query, qtype, rank, pk, "", f"error: {str(e)[:80]}", title, company, location, now_iso()]); n_err += 1
                    print(f"  {rank:3d} ERROR {str(e)[:90]} | {title[:40]}")
                hits_f.flush()
            info["queries_done"].append({"q": query, "type": qtype, "route": route, "cards_on_page": n_cards, "results": len(items), "new": n_new, "repeat": n_rep, "errors": n_err})
            with open(os.path.join(run_dir, "run_info.json"), "w", encoding="utf-8") as f:
                json.dump(info, f, indent=1)
            pause(4.0, 8.0)                                            # between queries
    finally:
        info["finished"] = now_iso()
        with open(os.path.join(run_dir, "run_info.json"), "w", encoding="utf-8") as f:
            json.dump(info, f, indent=1)
        hits_f.close()
        book = write_workbook(run_dir, args.area, run_id)
        print(f"\nRun folder: {run_dir}")
        if book:
            print(f"Workbook:   {book}")
        for qd in info["queries_done"]:
            print(f"  {qd['results']:4d} results  {qd['new']:4d} new  {qd['repeat']:4d} repeat  {qd['errors']:3d} errors  {qd['q']}")
        print(f"  total: {sum(q['results'] for q in info['queries_done'])} results, {sum(q['new'] for q in info['queries_done'])} distinct listings saved")
        try:
            driver.quit()
        except WebDriverException:
            pass


if __name__ == "__main__":
    main()
