#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
PubMed（複数検索式 or ジャーナルOR）→ Gemini(邦題+4点要約, 1コール/論文) → Gmail送信
- 毎日1回の実行想定（GitHub Actionsなど）
- 送信済みPMIDは sent_pmids.json で重複防止（初回登録日時 added_at を記録）
- 要約は Google AI Studio の gemini-(1.5|2.5)-flash を想定
"""

import os, json, time, ssl, smtplib, requests, re
from string import Template
from datetime import datetime, timedelta, timezone
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from xml.etree import ElementTree as ET
from google import genai

# ========= 環境変数 =========
GEMINI_MODEL = os.getenv("GEMINI_MODEL", "gemini-2.5-flash")
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY")  # AI StudioのAPIキー
JOURNALS = [j.strip() for j in os.getenv("JOURNALS", "").split(",") if j.strip()]
RECIPIENT = os.getenv("RECIPIENT_EMAIL", os.getenv("GMAIL_ADDRESS", ""))
GMAIL_ADDRESS = os.getenv("GMAIL_ADDRESS", "")
GMAIL_APP_PASSWORD = os.getenv("GMAIL_APP_PASSWORD", "")
PUBMED_TOOL_EMAIL = os.getenv("PUBMED_TOOL_EMAIL", GMAIL_ADDRESS)  # eutils &emailに使用（推奨）
NCBI_API_KEY = os.getenv("NCBI_API_KEY", "")  # 任意（レート上限UP）
SLEEP_BETWEEN_CALLS = float(os.getenv("SLEEP_BETWEEN_CALLS", "0.3"))  # 無料枠配慮
WINDOW_DAYS = int(os.getenv("WINDOW_DAYS", "2"))  # EDATの固定ウィンドウ（取りこぼし低減）

# ========= PubMed E-utilities =========
EUTILS_BASE = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/"
TOOL_NAME = "pubmed-daily-digest"
HEADERS = {"User-Agent": TOOL_NAME}

# ========= 状態保存 =========
STATE_PATH = "sent_pmids.json"

def load_sent_state():
    """sent_pmids.json を {pmid: {added_at: str}} で読み込む（旧listにも後方互換）"""
    if not os.path.exists(STATE_PATH):
        return {}
    try:
        with open(STATE_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            # 旧形式：["pmid", ...] → 新形式へ
            return {pmid: {"added_at": None} for pmid in data}
        if isinstance(data, dict):
            return data
    except Exception:
        pass
    return {}

def save_sent_state(state: dict):
    with open(STATE_PATH, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=2, sort_keys=True)

# ========= PubMed検索 =========
def build_journal_query(journals):
    # PubMedジャーナルフィールド[ta]でOR結合（完全名 or 略称）
    parts = [f'("{j}"[ta])' for j in journals]
    return "(" + " OR ".join(parts) + ")"

def _edat_window_params():
    # UTC基準の日付で固定窓（例：今日と過去N日）を作る
    utc_today = datetime.now(timezone.utc).date()
    mindate = (utc_today - timedelta(days=WINDOW_DAYS)).strftime("%Y/%m/%d")
    maxdate = utc_today.strftime("%Y/%m/%d")
    return {"datetype": "edat", "mindate": mindate, "maxdate": maxdate}

def pubmed_esearch(term):
    # 固定ウィンドウで検索（再実行しても窓がぶれない）
    params = {
        "db": "pubmed",
        "term": term,
        "retmode": "json",
        "retmax": "500",
        "sort": "pub_date",
        "tool": TOOL_NAME,
        "email": PUBMED_TOOL_EMAIL,
        **_edat_window_params(),
    }
    if NCBI_API_KEY:
        params["api_key"] = NCBI_API_KEY
    r = requests.get(EUTILS_BASE + "esearch.fcgi", params=params, headers=HEADERS, timeout=30)
    r.raise_for_status()
    data = r.json()
    return data.get("esearchresult", {}).get("idlist", [])

def pubmed_efetch(pmids):
    if not pmids:
        return ""
    params = {
        "db": "pubmed",
        "id": ",".join(pmids),
        "rettype": "abstract",
        "retmode": "xml",
        "tool": TOOL_NAME,
        "email": PUBMED_TOOL_EMAIL,
    }
    if NCBI_API_KEY:
        params["api_key"] = NCBI_API_KEY
    r = requests.get(EUTILS_BASE + "efetch.fcgi", params=params, headers=HEADERS, timeout=60)
    r.raise_for_status()
    return r.text

def load_multi_queries():
    """SEARCH_QUERIES（複数行・---区切り）を分割"""
    raw = os.getenv("SEARCH_QUERIES", "").strip()
    if not raw:
        return []
    parts = re.split(r"(?m)^\s*---\s*$", raw)
    return [p.strip() for p in parts if p.strip()]

def pubmed_multi_esearch_all(queries):
    """複数クエリを順に検索し、PMIDを重複排除して返す"""
    all_pmids = []
    seen = set()
    for q in queries:
        ids = pubmed_esearch(q)
        for pmid in ids:
            if pmid not in seen:
                seen.add(pmid)
                all_pmids.append(pmid)
        time.sleep(0.2)  # polite
    return all_pmids

# ========= 文字列整形/抽出 =========
def _norm_ws(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "")).strip()

def _itertext(elem) -> str:
    if elem is None:
        return ""
    return _norm_ws("".join(elem.itertext()))

def _prefer_abbrev(art) -> str:
    for path in [".//Journal/ISOAbbreviation",
                 ".//MedlineJournalInfo/MedlineTA",
                 ".//Journal/Title"]:
        val = art.findtext(path)
        if val and val.strip():
            return _norm_ws(val)
    return ""

# --- 日付整形ヘルパー ---
_MONTH_ABBR = {
    "1":"Jan","01":"Jan","Jan":"Jan","January":"Jan",
    "2":"Feb","02":"Feb","Feb":"Feb","February":"Feb",
    "3":"Mar","03":"Mar","Mar":"Mar","March":"Mar",
    "4":"Apr","04":"Apr","Apr":"Apr","April":"Apr",
    "5":"May","05":"May","May":"May",
    "6":"Jun","06":"Jun","Jun":"Jun","June":"Jun",
    "7":"Jul","07":"Jul","Jul":"Jul","July":"Jul",
    "8":"Aug","08":"Aug","Aug":"Aug","August":"Aug",
    "9":"Sep","09":"Sep","Sep":"Sep","September":"Sep",
    "10":"Oct","Oct":"Oct","October":"Oct",
    "11":"Nov","Nov":"Nov","November":"Nov",
    "12":"Dec","Dec":"Dec","December":"Dec",
}
def _fmt_date(y, m, d):
    y = (y or "").strip()
    m = _MONTH_ABBR.get((m or "").strip(), (m or "").strip())
    d = (d or "").strip()
    if y and m and d:
        if d.isdigit() and len(d) == 1:
            d = f"0{d}"
        return f"{y} {m} {d}"
    if y and m:
        return f"{y} {m}"
    return y or ""

def _extract_pubdate_display(art):
    for ad in art.findall(".//Article/ArticleDate"):
        dt = (ad.attrib or {}).get("DateType", "").lower()
        if dt == "electronic":
            return _fmt_date(ad.findtext("Year"), ad.findtext("Month"), ad.findtext("Day"))
    ad = art.find(".//Article/ArticleDate")
    if ad is not None:
        s = _fmt_date(ad.findtext("Year"), ad.findtext("Month"), ad.findtext("Day"))
        if s: return s
    y = art.findtext(".//JournalIssue/PubDate/Year")
    m = art.findtext(".//JournalIssue/PubDate/Month")
    d = art.findtext(".//JournalIssue/PubDate/Day")
    s = _fmt_date(y, m, d)
    if s: return s
    md = (art.findtext(".//JournalIssue/PubDate/MedlineDate") or "").strip()
    if md: return md
    for status in ("pubmed", "entrez", "medline"):
        ppd = art.find(f".//History/PubMedPubDate[@PubStatus='{status}']")
        if ppd is not None:
            return _fmt_date(ppd.findtext("Year"), ppd.findtext("Month"), ppd.findtext("Day"))
    return ""

def _extract_pubtypes(art):
    pts, seen = [], set()
    for pt in art.findall(".//PublicationTypeList/PublicationType"):
        t = (pt.text or "").strip()
        if t and t not in seen:
            seen.add(t)
            pts.append(t)
    return pts

PT_JA_MAP = {
    "Randomized Controlled Trial":"無作為化比較試験",
    "Systematic Review":"システマティックレビュー",
    "Meta-Analysis":"メタアナリシス",
    "Clinical Trial":"臨床試験",
    "Clinical Trial, Phase II":"第II相臨床試験",
    "Clinical Trial, Phase III":"第III相臨床試験",
    "Review":"総説",
    "Guideline":"ガイドライン",
    "Practice Guideline":"診療ガイドライン",
    "Multicenter Study":"多施設研究",
    "Comparative Study":"比較研究",
    "Observational Study":"観察研究",
    "Case Reports":"症例報告",
    "Editorial":"編集者寄稿",
    "Letter":"レター",
}
def _format_pt_for_display(pts):
    lang = os.getenv("PT_DISPLAY_LANG", "en").lower()
    if lang == "ja":
        return ", ".join(PT_JA_MAP.get(p, p) for p in pts)
    return ", ".join(pts)

# --- 国名抽出（エイリアスとTLDでロバスト化） ---
COUNTRY_ALIASES = {
    # 英語表記・別名 → 正規化（表示は右側の文字列）
    "usa":"USA","united states":"USA","united states of america":"USA","u.s.a.":"USA",
    "uk":"UK","united kingdom":"UK","england":"UK","scotland":"UK","wales":"UK","northern ireland":"UK",
    "republic of korea":"South Korea","south korea":"South Korea","korea, republic of":"South Korea","korea":"South Korea",
    "pr china":"China","p.r. china":"China","people's republic of china":"China","china":"China",
    "japan":"Japan","germany":"Germany","france":"France","italy":"Italy","spain":"Spain",
    "netherlands":"Netherlands","switzerland":"Switzerland","sweden":"Sweden","norway":"Norway",
    "denmark":"Denmark","finland":"Finland","austria":"Austria","belgium":"Belgium","ireland":"Ireland",
    "canada":"Canada","australia":"Australia","singapore":"Singapore","taiwan":"Taiwan","hong kong":"Hong Kong",
    "india":"India","thailand":"Thailand","malaysia":"Malaysia","philippines":"Philippines","indonesia":"Indonesia",
    "vietnam":"Vietnam","israel":"Israel","turkey":"Türkiye","türkiye":"Türkiye",
    "saudi arabia":"Saudi Arabia","united arab emirates":"UAE","uae":"UAE","qatar":"Qatar","kuwait":"Kuwait","iran":"Iran",
    "brazil":"Brazil","argentina":"Argentina","chile":"Chile","mexico":"Mexico","colombia":"Colombia","peru":"Peru",
    "south africa":"South Africa","egypt":"Egypt"
}

TLD_COUNTRY_MAP = {
    "jp":"Japan","uk":"UK","de":"Germany","fr":"France","it":"Italy","es":"Spain","nl":"Netherlands","ch":"Switzerland",
    "se":"Sweden","no":"Norway","dk":"Denmark","fi":"Finland","at":"Austria","be":"Belgium","ie":"Ireland",
    "ca":"Canada","au":"Australia","cn":"China","kr":"South Korea","tw":"Taiwan","sg":"Singapore","hk":"Hong Kong",
    "in":"India","tr":"Türkiye","sa":"Saudi Arabia","ae":"UAE","qa":"Qatar","kw":"Kuwait","il":"Israel","ir":"Iran",
    "br":"Brazil","ar":"Argentina","cl":"Chile","mx":"Mexico","co":"Colombia","pe":"Peru","za":"South Africa","eg":"Egypt",
    "us":"USA"
}

def _normalize_country(name: str) -> str:
    if not name: return ""
    key = re.sub(r"\s+", " ", name.strip().lower())
    return COUNTRY_ALIASES.get(key, name.strip())

def _extract_country_from_aff(aff: str) -> str:
    """Affiliationから国名を推定。メールTLD→末尾トークン→全体スキャンの順で判定。"""
    if not aff:
        return ""
    txt = aff

    # 1) メールアドレスのTLDから推定
    m = re.search(r'@[\w\.-]+\.(\w+)', txt)
    if m:
        tld = m.group(1).lower()
        if tld in TLD_COUNTRY_MAP:
            return TLD_COUNTRY_MAP[tld]

    # 2) 末尾側の ; / , 区切りから国名らしいトークンを拾う
    tail = re.split(r'[;]', txt)[-1]  # ; の右側を優先
    tokens = [t.strip(" .,") for t in tail.split(",") if t.strip(" .,")]
    for tok in reversed(tokens):
        norm = _normalize_country(tok)
        # エイリアスにヒット、または一般的な国名トークンなら採用
        if norm != tok or norm in COUNTRY_ALIASES.values():
            return COUNTRY_ALIASES.get(norm.lower(), norm)
        if 2 <= len(tok) <= 40 and re.match(r"^[A-Za-zÀ-ÿ .'-]+$", tok):
            return tok  # 見た目が国名っぽければ採用

    # 3) 全体テキストから既知国名エイリアスを検索
    for alias in sorted(COUNTRY_ALIASES.keys(), key=len, reverse=True):
        if re.search(rf'(?i)(^|[,\s;]){re.escape(alias)}([,\s.;]|$)', txt):
            return COUNTRY_ALIASES[alias]

    return ""

def parse_records(xml_text):
    if not xml_text:
        return []
    root = ET.fromstring(xml_text)
    results = []
    for art in root.findall(".//PubmedArticle"):
        pmid = (art.findtext(".//PMID") or "").strip()

        # タイトル（<i>や<sup>を含めて）
        title = _itertext(art.find(".//Article/ArticleTitle"))
        if len(title) < 2:
            print("WARN: suspicious title for PMID", pmid, "->", repr(title))

        # アブストラクト
        texts = []
        for abs_elem in art.findall(".//Abstract/AbstractText"):
            label = abs_elem.attrib.get("Label") if abs_elem.attrib else None
            txt = _itertext(abs_elem)
            if not txt: continue
            texts.append(f"{label}: {txt}" if label else txt)
        abstract = "\n".join(texts)

        # --- 著者（筆頭のみ + 2名以上なら", et al."）＋ 国名のみ（不明なら付けない） ---
        authors_nodes = art.findall(".//AuthorList/Author")
        first_author_name, counted, aff_raw = "", 0, ""

        for au in authors_nodes:
            last = au.findtext("LastName") or ""
            init = au.findtext("Initials") or ""
            collective = au.findtext("CollectiveName") or ""
            if last or init:
                name = f"{last} {init}".strip()
                if not first_author_name:
                    first_author_name = name
                    aff_elem = au.find("AffiliationInfo/Affiliation")
                    aff_raw = _itertext(aff_elem) if aff_elem is not None else ""
                counted += 1
            elif collective:
                if not first_author_name:
                    first_author_name = collective
                counted += 1

        # 筆頭にAffiliationが無ければ記事全体からフォールバック
        if not aff_raw:
            any_aff = art.find(".//AffiliationInfo/Affiliation")
            aff_raw = _itertext(any_aff) if any_aff is not None else ""

        country = _extract_country_from_aff(aff_raw)  # 不明なら "" が返る

        authors_display = first_author_name or ""
        if counted >= 2 and authors_display:
            authors_display += ", et al."
        if country:
            authors_display += f"（{country}）"

        authors_line = authors_display  # ← このauthors_lineをresults.appendに渡す
        
        # ジャーナル（略称優先）
        journal = _prefer_abbrev(art)

        # Publication Type / 発行日 / DOI
        pubtypes = _extract_pubtypes(art)
        pubdate  = _extract_pubdate_display(art)
        doi = ""
        for aid in art.findall(".//ArticleIdList/ArticleId"):
            if (aid.attrib or {}).get("IdType", "").lower() == "doi":
                doi = (aid.text or "").strip()
                break

        results.append({
            "pmid": pmid,
            "title": title,
            "authors": authors_line,
            "journal": journal,
            "pubdate": pubdate,
            "doi": doi,
            "url": f"https://pubmed.ncbi.nlm.nih.gov/{pmid}/",
            "abstract": abstract,
            "pt": pubtypes,
        })
    return results

# ========= Gemini（1回で邦題＋4点要約） =========
def _resp_to_text(resp) -> str:
    if getattr(resp, "text", None):
        return resp.text
    parts = []
    try:
        for c in getattr(resp, "candidates", []) or []:
            for p in getattr(c.content, "parts", []) or []:
                if getattr(p, "text", None):
                    parts.append(p.text)
    except Exception:
        pass
    return "\n".join(parts)

def _force_json(text: str) -> dict:
    if not text:
        return {}
    m = re.search(r"\{[\s\S]*\}", text)
    raw = m.group(0) if m else text
    try:
        data = json.loads(raw)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}

def _format_bullets(lines, target=4):
    xs = [str(x).strip() for x in (lines or []) if str(x).strip()]
    xs = [("・" + x.lstrip("・-•*・ 　")).strip() for x in xs]
    xs = xs[:target]
    while len(xs) < target:
        xs.append("・（要約が不足しています）")
    xs = [x if len(x) <= 150 else (x[:147] + "…") for x in xs]
    return xs

PROMPT_TEMPLATE = Template("""You are a specialized summarizer for radiation oncology literature, tasked with creating concise Japanese summaries for busy radiation oncologists. Your output must be a strict JSON object.

### JSON Output Format
- **title_ja**: A Japanese title (30-45 characters, ending with a noun, compressing any lengthy subtitles, and including the study design from the original title **only if explicitly mentioned**).
- **bullets**: An array of 4 or 5 bullet points, each 60-120 characters long.

### Key Rules
- **Fact Extraction Only**: Summarize only the facts present in the provided title and abstract. Do not add external knowledge, rephrase information with different meanings, or make assumptions.
- **Strictly JSON**: Output only the JSON object. Do not include any preceding or trailing text, or code blocks.

### Language and Notation Policy
- **International Abbreviations**: Use the original English for specific abbreviations like OS, PFS, LC, HR, CI, CR/PR, ORR, CTCAE, SUVmax, Gy, fx, SBRT/IMRT/VMAT/SIB/PBT, RT/CRT.
- **Numerals & Units**: Use original numerals and units. If a value is not specified, state "数値記載なし".
- **Chemicals/Tracers/Drugs**: Keep original notation (e.g., [18F], [68Ga], FAPI-46, nivolumab).
- **General Terms**: Translate common English words into Japanese (e.g., patients→患者, toxicity→毒性, bleeding→出血, ulcer(s)→潰瘍).
- **Slash Notation**: Naturalize expressions like "A/B" into "AやB" or "A・B". Replace "and/or" with "および／または" and "vs" with "対".
- **Dose Fractionation**: Format dose fractionation in standard Japanese style (e.g., 5 x 7 Gy becomes "7 Gy × 5回").

### Summarization Focus
- **Target**: Cancer type, stage, patient count, inclusion criteria.
- **Intervention**: Dose (Gy), fractionation (fx), site, modality (IMRT/VMAT/SBRT/SRS/particle therapy), concurrent therapy.
- **Outcomes**: OS, PFS, LC, response rate, HR/CI, p-value, follow-up period.
- **Safety**: CTCAE grade, adverse events.
- **Imaging**: Nuclide/tracer, diagnostic metrics.
- **Design**: Phase, randomization, single-arm, multi-institutional.

### Instructions for creating "bullets"
- Create 4 or 5 bullet points.
- Each bullet point must be between 60 and 120 characters in length.
- Summarize findings, avoiding interpretation or advice.
- When a summary exceeds 120 characters, prioritize the removal of less critical information like p-values or HR/CI to fit the character limit.
- The final bullet point should summarize the conclusion or main takeaway as stated in the abstract.

English Title:
$TITLE

Abstract:
$ABSTRACT
""")

def summarize_title_and_bullets(title: str, abstract: str) -> dict:
    client = genai.Client()  # GEMINI_API_KEY は環境変数から
    model_name = os.getenv("GEMINI_MODEL", "gemini-2.5-flash")
    prompt = PROMPT_TEMPLATE.substitute(
        TITLE=title,
        ABSTRACT=(abstract[:7000] if abstract else "")
    )
    try:
        resp = client.models.generate_content(model=model_name, contents=prompt)
        text = (_resp_to_text(resp) or "").strip()
        data = _force_json(text)
    except Exception:
        data = {}

    title_ja = str((data.get("title_ja") or "")).strip()
    bullets  = _format_bullets(data.get("bullets"))

    title_ja = title_ja.lstrip("・-•*[]() 　")
    if title_ja.endswith(("。","．",".")):
        title_ja = title_ja[:-1]
    if not title_ja:
        title_ja = "（邦題生成に失敗）"

    return {"title_ja": title_ja, "bullets": bullets}

# ========= メール整形・送信 =========
def build_email_body(date_jst_str, items):
    lines = []
    lines.append("新着論文AI要約配信\n")
    lines.append("放射線腫瘍学\n\n")
    lines.append(f"本日の新着論文は{len(items)}件です。\n\n")
    for i, it in enumerate(items, 1):
        lines.append(f"[論文{i}]")
        lines.append(f"原題：{str(it.get('title',''))}")
        lines.append(f"邦題（AI要約）：{str(it.get('title_ja',''))}")
        if it.get('authors'):
            lines.append(f"著者：{str(it.get('authors',''))}")
        lines.append(f"雑誌名：{str(it.get('journal',''))}")
        lines.append(f"発行日：{str(it.get('pubdate',''))}")
        if it.get("pt"):
            lines.append(f"文献種別：{_format_pt_for_display(it.get('pt', []))}")
        lines.append(f"Pubmed：{str(it.get('url',''))}")
        lines.append(f"DOI：{str(it.get('doi','') or '-')}")
        lines.append("要約（AI生成）：")
        lines.append(str(it.get('summary','')))
        lines.append("\n")
    return "\n".join(lines)

def send_via_gmail(subject, body):
    if not (GMAIL_ADDRESS and GMAIL_APP_PASSWORD and RECIPIENT):
        raise RuntimeError("Gmail送信に必要な環境変数が不足しています。")
    msg = MIMEMultipart()
    msg["From"] = GMAIL_ADDRESS
    msg["To"] = RECIPIENT
    msg["Subject"] = subject
    msg.attach(MIMEText(body, "plain", "utf-8"))

    context = ssl.create_default_context()
    with smtplib.SMTP_SSL("smtp.gmail.com", 465, context=context) as server:
        server.login(GMAIL_ADDRESS, GMAIL_APP_PASSWORD)
        server.sendmail(GMAIL_ADDRESS, [RECIPIENT], msg.as_string())

# ========= メイン =========
def main():
    print("=== PubMed論文収集開始 ===")

    queries = load_multi_queries()
    if queries:
        pmids = pubmed_multi_esearch_all(queries)
    else:
        # フォールバック：JOURNALSをOR結合
        if not JOURNALS:
            raise SystemExit("環境変数 JOURNALS か SEARCH_QUERIES のいずれかを設定してください。")
        pmids = pubmed_esearch(build_journal_query(JOURNALS))

    print(f"検索結果（重複前）: {len(pmids)}件")

    # 送信済み状態のロード
    state = load_sent_state()
    sent_set = set(state.keys())

    # 未送信のみ
    new_pmids = [p for p in pmids if p not in sent_set]
    print(f"新規論文数: {len(new_pmids)}件")

    items = []
    if new_pmids:
        xml = pubmed_efetch(new_pmids)
        records = parse_records(xml)

        # JSTの現在時刻（ISO8601）を初回登録に記録
        jst = timezone(timedelta(hours=9))
        now_jst_iso = datetime.now(jst).isoformat(timespec="seconds")

        print(f"\n{len(records)}件の新規論文を処理")
        for idx, rec in enumerate(records, 1):
            # 初回登録日時を state に保存（メールには出さない）
            if rec["pmid"] not in state or not isinstance(state.get(rec["pmid"]), dict):
                state[rec["pmid"]] = {"added_at": now_jst_iso}
            elif not state[rec["pmid"]].get("added_at"):
                state[rec["pmid"]]["added_at"] = now_jst_iso

            # AI要約
            print(f"要約中 ({idx}/{len(records)}): {rec['title'][:60]}...")
            data = summarize_title_and_bullets(rec["title"], rec["abstract"] or "")
            rec["title_ja"] = data["title_ja"]
            rec["summary"]  = "\n".join(data["bullets"]) if rec["abstract"] else "・この論文にはPubMed上でアブストラクトが見つかりません"

            time.sleep(SLEEP_BETWEEN_CALLS)
            items.append(rec)

        # 状態保存（added_atを含む）
        save_sent_state(state)

    # メール送信（0件でも通知）
    print("\n=== メール送信 ===")
    jst = timezone(timedelta(hours=9))
    today = datetime.now(jst).strftime("%Y-%m-%d")
    count = len(items)
    subject = f"【PubMed論文AI要約配信：新着{count}本】放射線腫瘍学 {today}"
    body = build_email_body(today, items)
    send_via_gmail(subject, body)
    print("\n=== 処理完了 ===")

if __name__ == "__main__":
    main()
