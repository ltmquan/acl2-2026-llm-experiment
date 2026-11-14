#!/usr/bin/env python3
"""Grader for tool-aes-mir (written before any run).

Usage: grade.sh <work-dir> [--adapter <grader-aes-adapter.lisp>]

Requirements (prompt numbering):
 R1 /work/subject/: own adaptation of fixslice32.rs as a cargo crate, ADAPTATION.md lists every difference
    -> mechanical prechecks (crate, ADAPTATION.md, a .rs file derived from fixslice32.rs) and a diff against the
    pristine file for the human (CHECKLIST R1); always MANUAL when the prechecks pass.
 R2 Charon --mir elaborated ULLBC JSON in /work/subject/, command in /work/README.md
    -> JSON found, options recorded in it (ullbc, mir=Elaborated, no monomorphization), the crate sources
    embedded in it equal the current files, the README command re-run with our Charon gives the same JSON
    (ignoring dest_dir/dest_file).  MANUAL only if the command cannot be extracted or run.
 R3 MIR semantics + importer certify; an import test book parses the JSON at certification time
    -> certification (as R6) + a certified book that names the JSON file; the rest MANUAL (CHECKLIST R3).
 R4 interpreter reproduces FIPS-197 C.1 and B, decrypt inverts both  -> grade-r4.lisp via the adapter.
 R5 66 inputs agree with aes::aes-128-encrypt  -> grade-r5.lisp via the adapter (our own 66 inputs).
    Without --adapter, R4 and R5 are MANUAL: write the adapter from the README (CHECKLIST R4/R5) and re-run.
 R6 all books certify with cert.pl.
"""
import glob, gzip, json, os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ACL2 = os.environ.get("GRADER_ACL2", "/opt/acl2/saved_acl2")
CERT = os.environ.get("GRADER_CERT", "/opt/acl2/books/build/cert.pl")
CRATE = os.environ.get("GRADER_AES_CRATE") or next(
    (p for p in ("/opt/inputs/aes-0.9.1.crate", "/home/user/acl2-exp/toolchain/aes-src/aes-0.9.1.crate")
     if os.path.exists(p)), None)
def charon_bin():
    c = os.environ.get("GRADER_CHARON") or shutil.which("charon")
    if not c:
        p = "/home/user/acl2-exp/toolchain/stage-charon/opt/charon/bin/charon"
        c = p if os.path.exists(p) else None
    return c
GRADER_FILES = ("grade-r4.lisp", "grade-r5.lisp", "grader-aes-adapter.lisp")
import os, re, shutil, subprocess, sys, tempfile
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


# ---------------------------------------------------------------- R2 helpers
def load_json(p):
    try:
        if p.endswith(".gz"):
            with gzip.open(p, "rt") as fh: return json.load(fh)
        with open(p) as fh: return json.load(fh)
    except Exception:
        return None

def charon_files(subj):
    out = []
    for p in glob.glob(os.path.join(subj, "**", "*"), recursive=True):
        if "/target/" in p or not os.path.isfile(p): continue
        if re.search(r"\.(json|ullbc|llbc)(\.gz)?$", p):
            j = load_json(p)
            if isinstance(j, dict) and "charon_version" in j and "translated" in j:
                out.append((p, j))
    return out

def normalize(j, roots):
    """drop the output-path options; replace the copy's path by /work"""
    j = json.loads(json.dumps(j))
    o = j.get("translated", {}).get("options", {})
    for k in ("dest_dir", "dest_file"):
        o.pop(k, None)
    s = json.dumps(j, sort_keys=True)
    for r in roots:
        s = s.replace(r, "/work")
    return s

def readme_commands(readme):
    """charon command lines in README.md, continuation lines joined"""
    txt = open(readme, errors="replace").read().replace("\\\r\n", " ").replace("\\\n", " ")
    cmds = []
    for line in txt.splitlines():
        l = line.strip().lstrip("$").strip().strip("`").strip()
        if re.search(r"(^|[\s/&;(])charon\s+(rustc|cargo)\b", l) and re.search(r"--mir[ =]elaborated", l):
            cmds.append(l)
    return cmds

def grade_r2(d, tmp):
    subj = os.path.join(d, "subject")
    readme = os.path.join(d, "README.md")
    found = charon_files(subj) if os.path.isdir(subj) else []
    if not found:
        return ("FAIL", "no Charon JSON (charon_version/translated) in /work/subject"), None
    good = [(p, j) for p, j in found
            if j["translated"].get("options", {}).get("mir") == "Elaborated"
            and j["translated"].get("options", {}).get("ullbc") is True]
    if not good:
        return ("FAIL", "no JSON in /work/subject was produced with --ullbc --mir elaborated: " +
                ", ".join(f"{os.path.relpath(p, d)}: mir={j['translated'].get('options', {}).get('mir')} "
                          f"ullbc={j['translated'].get('options', {}).get('ullbc')}" for p, j in found)), None
    path, j = good[0]
    rel = os.path.relpath(path, d)
    opts = j["translated"]["options"]
    probs, notes = [], [f"{rel} (charon {j.get('charon_version')})"]
    if opts.get("monomorphize"):
        probs.append(f"{rel} was produced with --monomorphize (Section 6.2: no monomorphization)")
    if j.get("has_errors"):
        probs.append(f"{rel} records has_errors")
    # embedded crate sources equal the current files
    crate = j["translated"].get("crate_name")
    stale = []
    for f in j["translated"].get("files", []):
        if f.get("crate_name") != crate or f.get("contents") is None: continue
        name = f.get("name", {}).get("Local") if isinstance(f.get("name"), dict) else None
        if not name: continue
        cands = ([os.path.join(d, name[len("/work/"):])] if name.startswith("/work/")
                 else [os.path.join(subj, name), os.path.join(d, name)] if not name.startswith("/") else [name])
        cur = next((c for c in cands if os.path.isfile(c)), None)
        if cur is None or open(cur, errors="replace").read() != f["contents"]:
            stale.append(name)
    if stale:
        probs.append(f"{rel} is stale: embedded sources differ from the current files: {stale}")
    # README command
    if not os.path.exists(readme):
        return ("FAIL", "/work/README.md missing; " + "; ".join(probs)), path
    cmds = readme_commands(readme)
    if not cmds:
        probs.append("README.md has no charon command with --mir elaborated")
        return ("FAIL", "; ".join(probs)), path
    if probs:
        return ("FAIL", "; ".join(probs)), path
    # regenerate with the README command, in a second copy
    charon = charon_bin()
    if not charon:
        return ("MANUAL", f"no charon found; CHECKLIST R2: re-run `{cmds[0]}` and compare with {rel}"), path
    regen = os.path.join(tmp, "regen")
    shutil.copytree(d, os.path.join(regen, "work"), ignore=shutil.ignore_patterns("target", "*.cert", "*.fasl"))
    rw = os.path.join(regen, "work")
    out = os.path.join(regen, "regenerated.json")
    cmd = cmds[0].replace("/work/", rw + "/").replace("/work ", rw + " ")
    cmd = re.sub(r"--dest-file[ =]\S+", f"--dest-file {out}", cmd)
    if "--dest-file" not in cmd:
        cmd = re.sub(r"(charon\s+(?:rustc|cargo))", rf"\1 --dest-file {out}", cmd, count=1)
    env = dict(os.environ, PATH=os.path.dirname(charon) + os.pathsep + os.environ.get("PATH", ""),
               CARGO_NET_OFFLINE="true")
    log = os.path.join(d, "grader-logs", "r2-charon.log")
    os.makedirs(os.path.dirname(log), exist_ok=True)
    rc = None
    with open(log, "w") as fh:
        # run from /work/subject (the crate), and if that fails from /work (for a relative `cd subject`)
        for cwd in (os.path.join(rw, "subject"), rw):
            fh.write(f"$ cd {cwd} && {cmd}\n"); fh.flush()
            try:
                r = subprocess.run(["bash", "-c", cmd], cwd=cwd, env=env, stdout=fh,
                                   stderr=subprocess.STDOUT, timeout=3600)
                rc = r.returncode
            except subprocess.TimeoutExpired:
                rc = 124
            if rc == 0 and os.path.exists(out):
                break
    new = load_json(out) if os.path.exists(out) else None
    if rc != 0 or new is None:
        return ("MANUAL", f"the README command did not run here (exit {rc}, log {log}); CHECKLIST R2: run it "
                          f"by hand and compare the output with {rel}, ignoring dest_dir/dest_file"), path
    if normalize(new, [rw, d]) != normalize(j, [rw, d]):
        return ("FAIL", f"re-running the README command gives a different JSON than {rel} "
                        f"(regenerated: {out}; log {log})"), path
    return ("PASS", "; ".join(notes) + "; regenerated identically"), path

# ---------------------------------------------------------------- R1 helpers
def grade_r1(d, tmp):
    subj = os.path.join(d, "subject")
    probs = []
    if not os.path.isfile(os.path.join(subj, "Cargo.toml")): probs.append("subject/Cargo.toml missing")
    if not os.path.isfile(os.path.join(subj, "ADAPTATION.md")): probs.append("subject/ADAPTATION.md missing")
    rs = [p for p in glob.glob(os.path.join(subj, "**", "*.rs"), recursive=True) if "/target/" not in p]
    if not rs: probs.append("no .rs file under subject/")
    if probs: return ("FAIL", "; ".join(probs))
    logs = os.path.join(d, "grader-logs"); os.makedirs(logs, exist_ok=True)
    if not CRATE:
        return ("MANUAL", "pristine crate not found; CHECKLIST R1")
    pr = os.path.join(tmp, "pristine")
    os.makedirs(pr, exist_ok=True)
    subprocess.run(["tar", "xzf", CRATE, "-C", pr, "aes-0.9.1/src/soft/fixslice32.rs"], check=False)
    up = os.path.join(pr, "aes-0.9.1", "src", "soft", "fixslice32.rs")
    ufns = set(re.findall(r"\bfn\s+(\w+)", open(up).read()))
    best = max(rs, key=lambda p: len(ufns & set(re.findall(r"\bfn\s+(\w+)", open(p, errors="replace").read()))))
    mfns = set(re.findall(r"\bfn\s+(\w+)", open(best, errors="replace").read()))
    if len(ufns & mfns) < 10:
        return ("FAIL", f"no .rs file under subject/ shares the upstream function names (best: "
                        f"{os.path.relpath(best, d)}, {len(ufns & mfns)} shared)")
    with open(os.path.join(logs, "r1-adaptation.diff"), "w") as fh:
        subprocess.run(["diff", "-u", up, best], stdout=fh)
    with open(os.path.join(logs, "r1-adaptation-ignoring-whitespace.diff"), "w") as fh:
        subprocess.run(["diff", "-u", "-w", "-B", up, best], stdout=fh)
    with open(os.path.join(logs, "r1-functions.txt"), "w") as fh:
        fh.write(f"upstream only: {sorted(ufns - mfns)}\nadaptation only: {sorted(mfns - ufns)}\n"
                 f"both: {sorted(ufns & mfns)}\n")
    return ("MANUAL", f"prechecks passed ({os.path.relpath(best, d)}); CHECKLIST R1: compare "
                      f"{logs}/r1-adaptation*.diff and r1-functions.txt with subject/ADAPTATION.md")

# ---------------------------------------------------------------- main
def model_books(d):
    out = []
    for root, dirs, files in os.walk(d):
        dirs[:] = [x for x in dirs if x not in ("target", ".git", "grader-logs") and not x.startswith(".")]
        if os.path.relpath(root, d).split(os.sep)[0] == "subject" and os.path.relpath(root, d) != ".":
            continue
        for f in files:
            if f.endswith(".lisp") and not (root == d and f in GRADER_FILES):
                out.append(os.path.relpath(os.path.join(root, f), d)[:-5])
    return sorted(out)

def main():
    args = sys.argv[1:]
    adapter = None
    if "--adapter" in args:
        i = args.index("--adapter"); adapter = os.path.abspath(args[i + 1]); del args[i:i + 2]
    work = args[0]
    tmp = tempfile.mkdtemp(prefix="grade-tool-aes-mir-")
    d = os.path.join(tmp, "work")
    shutil.copytree(work, d, ignore=shutil.ignore_patterns(".git", "*.cert", "*.fasl", "*.port", "*.cert.out",
                                                           ".sys", "target"))
    print(f"GRADER: work copy in {d}")
    res = {}
    absw = []
    for root, _, files in os.walk(d):
        for f in files:
            if f.endswith((".lisp", ".acl2", ".lsp")) and '"/work/' in open(os.path.join(root, f), errors="replace").read():
                absw.append(os.path.relpath(os.path.join(root, f), d))
    linked = False
    if absw:
        if not os.path.exists("/work"):
            try:
                os.symlink(d, "/work"); linked = True
                print(f"GRADER: absolute /work paths in {absw}; /work -> {d} for this run")
            except OSError:
                print(f"GRADER: WARNING absolute /work paths in {absw} and /work cannot be created")
        else:
            print(f"GRADER: WARNING absolute /work paths in {absw}; they resolve to the existing /work")
    try:
        hits = banned_scan(d)
        if hits:
            for r in range(1, 7): res[r] = ("FAIL", "banned event: " + "; ".join(hits))
            return report(res)
        res[1] = grade_r1(d, tmp)
        res[2], jpath = grade_r2(d, tmp)
        # R6 (and R3): certify every model book
        books = model_books(d)
        print(f"GRADER: model books: {books}")
        failed = []
        for b in books:
            ok, log = certify(d, b)
            if not ok: failed.append(f"{b} ({reason(d, b, log)})")
        res[6] = ("PASS", f"{len(books)} books") if books and not failed else \
                 ("FAIL", "no books" if not books else "did not certify: " + "; ".join(failed))
        # R3
        if not books or failed:
            res[3] = ("FAIL", "books do not all certify")
        else:
            jn = os.path.basename(jpath) if jpath else None
            stem = re.sub(r"\.(json|ullbc|llbc)(\.gz)?$", "", jn) if jn else None
            itests = [b for b in books if stem and stem in open(os.path.join(d, b + ".lisp"), errors="replace").read()]
            if not itests:
                res[3] = ("FAIL", f"no certified book names the JSON file {jn}")
            else:
                res[3] = ("MANUAL", f"books certify; import test candidates {itests}; CHECKLIST R3: confirm the "
                                    "fixtypes and interpreter, and that the import test parses the JSON at "
                                    "certification time and compares with the interpreter tests' program")
        # R4, R5
        if adapter is None:
            for r in (4, 5):
                res[r] = ("MANUAL", "no --adapter: write grader-aes-adapter.lisp from README.md (CHECKLIST R4/R5, "
                                    f"template {HERE}/adapter-template.lisp) and re-run with --adapter")
        else:
            shutil.copy(adapter, os.path.join(d, "grader-aes-adapter.lisp"))
            for r, b in ((4, "grade-r4"), (5, "grade-r5")):
                shutil.copy(os.path.join(HERE, b + ".lisp"), d)
                ok, log = certify(d, b)
                if ok:
                    res[r] = ("PASS", "")
                else:
                    out = os.path.join(d, b + ".cert.out")
                    txt = open(out, errors="replace").read() if os.path.exists(out) else ""
                    fl = [" ".join(x.split())[:200] for x in re.findall(r"GRADER-FAIL[^\n]*(?:\n[^\n]+){0,2}", txt)]
                    res[r] = ("FAIL", "; ".join(fl[:5]) if fl else reason(d, b, log))
        report(res)
    finally:
        if linked: os.unlink("/work")

def report(res):
    allok = True
    for r in range(1, 7):
        st, why = res.get(r, ("FAIL", "not checked"))
        print(f"R{r} {st}" + (f" {why}" if why else ""))
        if st == "FAIL": allok = False
    n = {s: sum(1 for v in res.values() if v[0] == s) for s in ("PASS", "FAIL", "MANUAL")}
    print(f"SUMMARY tool-aes-mir: {n['PASS']} PASS, {n['FAIL']} FAIL, {n['MANUAL']} MANUAL")
    sys.exit(0 if allok else 1)

if __name__ == "__main__":
    main()
