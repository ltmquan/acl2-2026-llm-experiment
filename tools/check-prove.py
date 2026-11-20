#!/usr/bin/env python3
"""Checker for the prove tasks of the next experiments (fw-* with definitions and theorems, zfc-*).

Usage: python3 -I check-prove.py <work-dir> <task-dir>

<work-dir>  the folder holding the model's solution.lisp (the task folder itself); only solution.lisp is used
<task-dir>  the task folder NN-<paper>/exp4/<item>/: defs.lisp, targets.lisp, and admit.lisp / optional.lisp / cert.acl2 if present

Checks, in order:
 1. banned events in solution.lisp (skip-proofs, defaxiom, trust tags, redefinition, ...; for ZFC also
    direct zfc-table edits, table-redo and with-props);
 2. (include-book "defs") is present, and every other include is a community book (:dir :system);
 3. every form of admit.lisp appears, not under local, with the same kind, name, formals and body
    (declarations and hints may differ);
 4. every target appears, not under local, as a defthm (fw) or defthmz (zfc) with the same name and formula
    (rule classes, hints and, for defthmz, :props may differ);
 5. solution.lisp certifies with cert.pl next to our own copy of defs.lisp (and cert.acl2), with default
    cert flags, so a skip-proofs anywhere (for example defthme's fallback) fails certification.
Optional targets (optional.lisp) are reported but not required.
Exit 0 = all required checks pass.
"""
import os, re, shutil, subprocess, sys, tempfile

IMAGES = {  # task family -> (acl2 image, cert.pl)
    "fw":  ("/opt/acl2r/saved_acl2r", "/opt/acl2/books/build/cert.pl"),
    "zfc": ("/opt/acl2-master/saved_acl2", "/opt/acl2-master/books/build/cert.pl"),
}
BANNED = (r"skip-proofs|defaxiom|defttag|set-ld-redefinition-action|skip-proofs-okp|:ttags|set-skip-proofs|"
          r"trust-tag|define-trusted-clause-processor|defun-unsound|sys-call|reset-prehistory|\bredef\b|set-cbd|"
          r"progn!|defattach-system|set-raw-mode|\bdefstobj\b.*:congruent-to")
BANNED_ZFC = r"\(\s*table\s+zfc-table|table-redo|with-props"

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

def exported(forms):
    """Events visible after the book: top level or inside encapsulate/progn, never under local."""
    out = []
    def walk(f):
        if not isinstance(f, list) or not f or f[0] == "local":
            return
        if f[0] == "encapsulate":
            for g in f[2:]: walk(g)
        elif f[0] == "progn":
            for g in f[1:]: walk(g)
        else:
            out.append(f)
    for f in forms: walk(f)
    return out

def strip_package(x):  # ZF::FOO and FOO are the same symbol in a ZF book
    if isinstance(x, str): return re.sub(r"^(zf|acl2)::", "", x)
    return [strip_package(y) for y in x]

def defn_key(f):
    """(kind name formals body) of a defun-like form, ignoring declarations, doc strings and hints."""
    return (f[0], f[1], f[2], f[-1])

def main():
    work, task = sys.argv[1], sys.argv[2]
    tid = os.path.basename(os.path.normpath(task))
    fam = "zfc" if tid.startswith("zfc-") else "fw"
    acl2, cert = IMAGES[fam]
    d = tempfile.mkdtemp(prefix=f"check-{tid}-")
    shutil.copy(os.path.join(work, "solution.lisp"), os.path.join(d, "solution.lisp"))
    shutil.copy(os.path.join(task, "defs.lisp"), os.path.join(d, "defs.lisp"))
    if os.path.exists(os.path.join(task, "cert.acl2")):
        shutil.copy(os.path.join(task, "cert.acl2"), d)
    src = open(os.path.join(d, "solution.lisp")).read()
    code = re.sub(r";[^\n]*", "", re.sub(r"#\|.*?\|#", " ", src, flags=re.S))
    for pat in [BANNED] + ([BANNED_ZFC] if fam == "zfc" else []):
        m = re.search(pat, code, re.I)
        if m:
            print(f"BANNED: {m.group(0)}"); print(d); sys.exit(2)
    forms = parse(tokens(src))
    top = [f[1] if isinstance(f, list) and len(f) == 2 and f[0] == "local" else f for f in forms]
    if not any(isinstance(f, list) and f[:2] == ["include-book", '"defs"'] for f in top):
        print('NO-INCLUDE: solution must (include-book "defs")'); print(d); sys.exit(3)
    def includes(x, acc):
        if isinstance(x, list):
            if x and x[0] == "include-book": acc.append(x)
            for y in x: includes(y, acc)
        return acc
    for f in includes(forms, []):
        if f[1:2] == ['"defs"']: continue
        if ":dir" in f and f[f.index(":dir") + 1:f.index(":dir") + 2] == [":system"]: continue
        print("BAD-INCLUDE: " + " ".join(map(str, f[:4]))); print(d); sys.exit(5)
    ev = [strip_package(f) for f in exported(forms)]
    bad = []
    # 3. definitions to admit
    ap = os.path.join(task, "admit.lisp")
    if os.path.exists(ap):
        have = {}
        for f in ev:
            if f[0] in ("defun", "defun-std", "defund", "defun-nx") and len(f) >= 4:
                have.setdefault(f[1], f)
        for a in parse(tokens(open(ap).read())):
            g = have.get(a[1])
            if g is None:
                bad.append(f"definition {a[1]} not admitted")
            elif (g[0].replace("defund", "defun"), g[1], g[2], g[-1]) != defn_key(a):
                bad.append(f"definition {a[1]} differs (kind, formals or body)")
    # 4. targets
    kinds = ("defthmz",) if fam == "zfc" else ("defthm", "defthmd", "defthm-std")
    thms = {}
    for f in ev:
        if f[0] in kinds and len(f) >= 3:
            thms.setdefault(f[1], f[2])
    def check_targets(path):
        res = []
        for t in parse(tokens(open(path).read())):
            t = strip_package(t)
            if t[1] not in thms: res.append((t[1], "missing"))
            elif thms[t[1]] != t[2]: res.append((t[1], "formula differs"))
            else: res.append((t[1], "ok"))
        return res
    req = check_targets(os.path.join(task, "targets.lisp"))
    bad += [f"{n}: {s}" for n, s in req if s != "ok"]
    op = os.path.join(task, "optional.lisp")
    opt = check_targets(op) if os.path.exists(op) else []
    if bad:
        print("MISMATCH: " + "; ".join(bad)); print(d); sys.exit(4)
    # 5. certify
    log = os.path.join(d, "check.log")
    with open(log, "w") as fh:
        r = subprocess.run(["perl", cert, "--acl2", acl2, "solution.lisp"], cwd=d, stdout=fh,
                           stderr=subprocess.STDOUT, timeout=4 * 3600)
    ok = r.returncode == 0 and os.path.exists(os.path.join(d, "solution.cert"))
    if not ok:
        print("FAILED: did not certify; see " + log); print(d); sys.exit(1)
    print(f"CERTIFIED with {acl2}; required targets matched: " + ", ".join(n for n, _ in req))
    for n, s in opt:
        print(f"optional {n}: {'proved' if s == 'ok' else s}")
    print(d); sys.exit(0)

if __name__ == "__main__":
    main()
