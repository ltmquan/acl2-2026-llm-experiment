#!/usr/bin/env python3
"""Grader for fw-multisets (written before any run).  Usage: grade.sh <work-dir>

Requirements (prompt numbering):
 R1 the library is /work/mset.lisp, package in /work/package.lsp, /work/cert.acl2 loads it  -> files present,
    and the library meets the prompt's specification: grade-r1-defs.lisp (guards, bequiv congruences, no list
    conversion in count/insert/delete), grade-r1-thms.lisp (each required theorem, our statement),
    the fixed-name witness theorems (count-diff-witness / bag-extensionality, subbag-witness /
    subbag-when-counts-le, count-le-when-subbag) are in grade-r1-thms; only if they fail, grade-r1-witness.lisp
    (generated) searches other witness functions and a success there is MANUAL; plus MANUAL: the documentation
    of the behavior on non-bags;
 R2 /work/mset-tests.lisp includes the library and evaluates each function with assert-event;
 R3 both books certify with cert.pl.
"""
import os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ACL2 = os.environ.get("GRADER_ACL2", "/opt/acl2/saved_acl2")
CERT = os.environ.get("GRADER_CERT", "/opt/acl2/books/build/cert.pl")
REQUIRED = ["bagp", "bfix", "bequiv", "empty", "emptyp", "count", "in", "insert", "insert-n", "delete",
            "delete-all", "cardinality", "support", "subbag", "sum", "union", "intersect", "diff", "from-list",
            "to-list"]
BANNED = (r"skip-proofs|defaxiom|defttag|set-ld-redefinition-action|skip-proofs-okp|:ttags|set-skip-proofs|"
          r"trust-tag|define-trusted-clause-processor|defun-unsound|sys-call|reset-prehistory|\bredef\b|set-cbd|"
          r"progn!|defattach-system|set-raw-mode|\bdefstobj\b.*:congruent-to|remove-untouchable|push-untouchable|"
          r"set-temp-touchable|with-raw-mode|include-raw")

# ---------------------------------------------------------------- s-expressions (from check-prove.py)
def tokens(s):
    s = re.sub(r"#\|.*?\|#", " ", s, flags=re.S)
    out, i = [], 0
    while i < len(s):
        c = s[i]
        if c == ";":
            j = s.find("\n", i); i = len(s) if j < 0 else j
        elif c.isspace():
            i += 1
        elif c in "()'`,":
            out.append(c); i += 1
        elif c == '"':
            j = i + 1
            while j < len(s) and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append(s[i:j + 1]); i = j + 1
        elif c == "|":
            j = s.find("|", i + 1); out.append(s[i:j + 1]); i = j + 1
        else:
            j = i
            while j < len(s) and not s[j].isspace() and s[j] not in "();\"'`,":
                j += 1
            out.append(s[i:j].lower()); i = j
    return out

def parse(toks):
    def rd(i):
        t = toks[i]
        if t == "(":
            lst, i = [], i + 1
            while toks[i] != ")":
                x, i = rd(i); lst.append(x)
            return lst, i + 1
        if t in ("'", "`", ","):
            x, i = rd(i + 1); return [{"'": "quote", "`": "quasiquote", ",": "unquote"}[t], x], i
        return t, i + 1
    forms, i = [], 0
    while i < len(toks):
        f, i = rd(i); forms.append(f)
    return forms

def unparse(x):
    if isinstance(x, list):
        if len(x) == 2 and x[0] == "quote": return "'" + unparse(x[1])
        return "(" + " ".join(unparse(y) for y in x) + ")"
    return x

def mentions(x, sym):
    if isinstance(x, list): return any(mentions(y, sym) for y in x)
    return x == sym or x.endswith("::" + sym)

# ---------------------------------------------------------------- shared steps
def sh(cmd, cwd, log, timeout):
    with open(log, "w") as fh:
        try:
            r = subprocess.run(cmd, cwd=cwd, stdout=fh, stderr=subprocess.STDOUT, timeout=timeout)
            return r.returncode
        except subprocess.TimeoutExpired:
            fh.write("\nGRADER: TIMEOUT\n"); return 124

def certify(d, book, timeout=4 * 3600):
    log = os.path.join(d, "grader-logs", book.replace("/", "_") + ".log")
    os.makedirs(os.path.dirname(log), exist_ok=True)
    rc = sh(["perl", CERT, "--acl2", ACL2, book], d, log, timeout)
    ok = rc == 0 and os.path.exists(os.path.join(d, book + ".cert"))
    return ok, log

def reason(book_dir, book, log):
    out = os.path.join(book_dir, book + ".cert.out")
    txt = open(out, errors="replace").read() if os.path.exists(out) else open(log, errors="replace").read()
    m = re.search(r"GRADER-FAIL:(.*?)(\n\n|$)", txt, re.S)
    if m: return " ".join(m.group(1).split())[:400]
    m = re.search(r"ACL2 Error[^\n]*in ([^\n]*)", txt)
    return ("ACL2 error in " + " ".join(m.group(1).split())[:200]) if m else "did not certify"

def banned_scan(d):
    hits = []
    for root, _, files in os.walk(d):
        for fn in files:
            if fn.endswith((".lisp", ".lsp", ".acl2")) and fn != "acl2-customization.lsp":  # not read by cert.pl
                p = os.path.join(root, fn)
                src = open(p, errors="replace").read()
                # cert.pl reads "; cert-flags:" / "cert_param:" comments, so check those before stripping comments
                m = re.search(r"cert[-_](?:flags|param)[^\n]*(?:skip-proofs|ttags|acl2x)", src, re.I)
                if m: hits.append(f"{os.path.relpath(p, d)}: {m.group(0)}")
                code = re.sub(r";[^\n]*", "", re.sub(r"#\|.*?\|#", " ", src, flags=re.S))
                m = re.search(BANNED, code, re.I)
                if m: hits.append(f"{os.path.relpath(p, d)}: {m.group(0)}")
    return hits


# ---------------------------------------------------------------- main
def flatten_events(forms):
    """non-local events at top level or inside progn/encapsulate/defsection"""
    out = []
    def walk(f):
        if not isinstance(f, list) or not f or not isinstance(f[0], str): return
        h = f[0].split("::")[-1]
        if h == "local": return
        if h in ("progn", "defsection", "encapsulate", "with-output", "skip-proofs"):
            for g in f[1:]: walk(g)
        else:
            out.append(f)
    for f in forms: walk(f)
    return out

def sym(name, pkg_of_file):
    return name if "::" in name else (f"mset::{name}" if pkg_of_file == "mset" else f"acl2::{name}")

def in_package(forms):
    for f in forms:
        if isinstance(f, list) and len(f) == 2 and f[0] == "in-package":
            return f[1].strip('"').lower()
    return "acl2"

def witness_candidates(forms):
    pkg = in_package(forms)
    cands = []
    for f in flatten_events(forms):
        h = f[0].split("::")[-1]
        if len(f) < 3 or not isinstance(f[1], str): continue
        if h == "defun-sk" and isinstance(f[2], list) and len(f[2]) == 2:
            sk = None
            for i, t in enumerate(f):
                if t == ":skolem-name" and i + 1 < len(f): sk = f[i + 1]
            cands.append(sym(sk or (f[1] + "-witness"), pkg))
        elif h in ("defun", "defund", "define", "defun-nx", "defund-nx") and isinstance(f[2], list):
            formals = [x[0] if isinstance(x, list) else x for x in f[2]]
            formals = [x for x in formals if isinstance(x, str) and not x.startswith("&")]
            if len(formals) == 2 and f[1].split("::")[-1] not in REQUIRED:
                cands.append(sym(f[1], pkg))
        elif h == "defchoose" and len(f) >= 4 and isinstance(f[3], list) and len(f[3]) == 2:
            cands.append(sym(f[1], pkg))
    seen = []
    for c in cands:
        if c not in seen: seen.append(c)
    return seen

def witness_book(cands):
    """fallback: the two witness statements with each candidate W (both argument orders), each tried by gr-thm
    (the model's rules, then :by / :use of each model theorem)"""
    forms = []
    i = 0
    for w in cands:
        for args in ("x y", "y x"):
            W = f"({w} {args})"
            i += 1
            forms.append(f"""(gr-thm gr-extensionality-{i}
  (implies (and (mset::bagp x) (mset::bagp y)
                (equal (mset::count {W} x) (mset::count {W} y)))
           (equal x y)))
(gr-thm gr-subbag-complete-{i}
  (implies (and (mset::bagp x) (mset::bagp y)
                (<= (mset::count {W} x) (mset::count {W} y)))
           (mset::subbag x y)))
(value-triple (cw "GRADER-OK candidate {i} is {W} GRADEREND~%"))""")
    body = "\n".join(forms)
    return f"""; Grader R1 (fw-multisets), generated by grade.py only when the fixed-name
; statements with count-diff-witness / subbag-witness fail: fallback search
; over each candidate witness function found in mset.lisp ({len(cands)}
; candidates).  A success here is reported as MANUAL, not PASS.
(in-package "ACL2")
(include-book "grader-mset-model-defs")

{body}
"""

def collect(book_dir, book):
    out = os.path.join(book_dir, book + ".cert.out")
    txt = open(out, errors="replace").read() if os.path.exists(out) else ""
    # a message runs from GRADER-OK / GRADER-FAIL to GRADEREND (fmt may wrap it over lines)
    msgs = [" ".join(m.replace("\\\n", "").replace("-\n", "-").split())
            for m in re.findall(r"^(GRADER-(?:OK|FAIL)\s.*?)\s*GRADEREND", txt, re.M | re.S)]
    oks = [m[len("GRADER-OK "):] for m in msgs if m.startswith("GRADER-OK ")]
    fails = [m[len("GRADER-FAIL "):] for m in msgs if m.startswith("GRADER-FAIL ")]
    return oks, fails

def main():
    work = sys.argv[1]
    tmp = tempfile.mkdtemp(prefix="grade-fw-multisets-")
    d = os.path.join(tmp, "work")
    shutil.copytree(work, d, ignore=shutil.ignore_patterns(".git", "*.cert", "*.fasl", "*.port", "*.cert.out",
                                                           ".sys"))
    print(f"GRADER: work copy in {d}")
    res = {}
    hits = banned_scan(d)
    if hits:
        for r in (1, 2, 3): res[r] = ("FAIL", "banned event: " + "; ".join(hits))
        return report(res)
    files = {f: os.path.exists(os.path.join(d, f)) for f in ("mset.lisp", "package.lsp", "cert.acl2",
                                                             "mset-tests.lisp")}
    # R3
    okl, logl = certify(d, "mset") if files["mset.lisp"] else (False, None)
    okt, logt = certify(d, "mset-tests") if files["mset-tests.lisp"] else (False, None)
    if okl and okt:
        res[3] = ("PASS", "")
    else:
        why = [f"{f} missing" for f in ("mset.lisp", "mset-tests.lisp") if not files[f]]
        if files["mset.lisp"] and not okl: why.append("mset: " + reason(d, "mset", logl))
        if files["mset-tests.lisp"] and not okt: why.append("mset-tests: " + reason(d, "mset-tests", logt))
        res[3] = ("FAIL", "; ".join(why))
    # R1
    manual = []
    probs = [f"{f} missing" for f in ("mset.lisp", "package.lsp", "cert.acl2") if not files[f]]
    if files["cert.acl2"] and not re.search(r"package\.lsp", open(os.path.join(d, "cert.acl2")).read()):
        probs.append("cert.acl2 does not load package.lsp")
    if files["package.lsp"] and not re.search(r'defpkg\s+"MSET"', open(os.path.join(d, "package.lsp")).read(), re.I):
        probs.append('package.lsp has no (defpkg "MSET" ...)')
    if not okl:
        probs.append("mset.lisp does not certify")
    else:
        for f in ("grader-mset-lib.lisp", "grader-mset-model-defs.lisp", "grade-r1-defs.lisp", "grade-r1-thms.lisp"):
            shutil.copy(os.path.join(HERE, f), d)
        books = ["grade-r1-defs", "grade-r1-thms"]
        fixed_fails = {}
        for b in books:
            ok, log = certify(d, b)
            if not ok:
                probs.append(f"{b} did not certify: {reason(d, b, log)}"); continue
            oks, fails = collect(d, b)
            for o in oks: print(f"  R1/{b} OK {o}")
            for f in fails: print(f"  R1/{b} FAIL {f}")
            for f in fails:
                key = f.split(": ")[0].strip().upper()
                alias = {"MSET::BAG-EXTENSIONALITY": "GR-BAG-EXTENSIONALITY",
                         "MSET::SUBBAG-WHEN-COUNTS-LE": "GR-SUBBAG-WHEN-COUNTS-LE"}
                key = alias.get(key, key)
                if key in ("GR-BAG-EXTENSIONALITY", "GR-SUBBAG-WHEN-COUNTS-LE"):
                    fixed_fails[key] = fixed_fails.get(key, "") + f + "; "
                else:
                    probs.append(f"{b}: {f[:160]}")
            if b == "grade-r1-thms":  # sanity: every check printed one line
                n = len(re.findall(r"^\(gr-", open(os.path.join(d, b + ".lisp")).read(), re.M))
                if len(oks) + len(fails) != n:
                    probs.append(f"{b}: {len(oks)} OK + {len(fails)} FAIL lines, expected {n} checks")
        # fallback: the witness statements failed with the prompt's names; search other witnesses
        if fixed_fails:
            cands = witness_candidates(parse(tokens(open(os.path.join(d, "mset.lisp"), errors="replace").read())))
            print(f"GRADER: fixed-name witness statements failed {sorted(fixed_fails)}; candidates: {cands}")
            found = {}
            if cands:
                open(os.path.join(d, "grade-r1-witness.lisp"), "w").write(witness_book(cands))
                ok, log = certify(d, "grade-r1-witness")
                if ok:
                    oks, _ = collect(d, "grade-r1-witness")
                    for o in oks: print(f"  R1/grade-r1-witness OK {o}")
                    found = {"GR-BAG-EXTENSIONALITY": any(o.startswith("GR-EXTENSIONALITY-") for o in oks),
                             "GR-SUBBAG-WHEN-COUNTS-LE": any(o.startswith("GR-SUBBAG-COMPLETE-") for o in oks)}
            for k, f in fixed_fails.items():
                if found.get(k):
                    manual.append(f"{k} fails with the prompt's witness name but holds with another witness "
                                  "(CHECKLIST: witness)")
                else:
                    probs.append(f"grade-r1-thms: {f[:160]}")
    if probs:
        res[1] = ("FAIL", "; ".join(probs))
    else:
        res[1] = ("MANUAL", "; ".join(manual + ["mechanical checks passed; CHECKLIST R1-M: confirm mset.lisp "
                                                "documents the behavior on non-bags"]))
    # R2
    res[2] = grade_r2(d, files, okt)
    report(res)

def grade_r2(d, files, okt):
    if not files["mset-tests.lisp"]: return ("FAIL", "mset-tests.lisp missing")
    if not okt: return ("FAIL", "mset-tests.lisp does not certify")
    forms = parse(tokens(open(os.path.join(d, "mset-tests.lisp"), errors="replace").read()))
    top = [g[1] if isinstance(g, list) and g[:1] == ["local"] else g for g in forms]
    if not any(isinstance(f, list) and len(f) >= 2 and f[0] == "include-book" and f[1].strip('"') == "mset"
               for f in top):
        return ("FAIL", 'mset-tests.lisp does not (include-book "mset")')
    pkg = in_package(forms)
    asserts = []
    def walk(f):
        if isinstance(f, list) and f:
            if isinstance(f[0], str) and f[0].split("::")[-1] in ("assert-event", "assert-equal"):
                asserts.append(f); return
            for g in f: walk(g)
    walk(forms)
    def mentions(x, fn):
        if isinstance(x, list): return any(mentions(y, fn) for y in x)
        return x == "mset::" + fn or (pkg == "mset" and x == fn)
    missing = [fn for fn in REQUIRED if not any(mentions(a, fn) for a in asserts)]
    if missing:
        return ("FAIL", f"no assert-event evaluates {missing}")
    return ("PASS", f"{len(asserts)} assertions cover all {len(REQUIRED)} functions")

def report(res):
    allok = True
    for r in (1, 2, 3):
        st, why = res.get(r, ("FAIL", "not checked"))
        print(f"R{r} {st}" + (f" {why}" if why else ""))
        if st == "FAIL": allok = False
    n = {s: sum(1 for v in res.values() if v[0] == s) for s in ("PASS", "FAIL", "MANUAL")}
    print(f"SUMMARY fw-multisets: {n['PASS']} PASS, {n['FAIL']} FAIL, {n['MANUAL']} MANUAL")
    sys.exit(0 if allok else 1)

if __name__ == "__main__":
    main()
