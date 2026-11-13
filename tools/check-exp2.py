#!/usr/bin/env python3
"""Checker for the ACL2-version experiment.

Usage: python3 -I check-exp2.py <solution.lisp> <given-dir> [acl2|acl2r]

<given-dir> contains:
  defs.lisp     the authors' definitions (proofs stripped) — our pristine copy
  targets.lisp  the target theorems, as (defthm NAME STATEMENT) forms (no hints)
The solution must (include-book "defs") and contain, for every target, a top-level
(defthm NAME ...) or (defthmd NAME ...) whose statement is identical (as an s-expression,
case-insensitive) to the target's. The checker copies the pristine defs.lisp next to the
solution, scans the solution for banned events, checks the targets, and certifies.
Exit 0 = all good.
"""
import os, re, shutil, subprocess, sys, tempfile

BANNED = re.compile(r"skip-proofs|defaxiom|defttag|set-ld-redefinition-action|skip-proofs-okp|:ttags|"
                    r"set-skip-proofs|trust-tag|define-trusted-clause-processor|defun-unsound|"
                    r"sys-call|reset-prehistory|\bredef\b|set-cbd|progn!", re.I)

def tokens(s):
    s = re.sub(r"#\|.*?\|#", " ", s, flags=re.S)
    out, i = [], 0
    while i < len(s):
        c = s[i]
        if c == ";":
            j = s.find("\n", i); i = len(s) if j < 0 else j
        elif c.isspace():
            i += 1
        elif c in "()":
            out.append(c); i += 1
        elif c == "'":
            out.append("'"); i += 1
        elif c == '"':
            j = i + 1
            while j < len(s) and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append(s[i:j + 1]); i = j + 1
        elif c == "|":
            j = s.find("|", i + 1); out.append(s[i:j + 1]); i = j + 1
        else:
            j = i
            while j < len(s) and not s[j].isspace() and s[j] not in "();\"":
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
        if t == "'":
            x, i = rd(i + 1); return ["quote", x], i
        return t, i + 1
    forms, i = [], 0
    while i < len(toks):
        f, i = rd(i); forms.append(f)
    return forms

def unlocal(f):
    while isinstance(f, list) and len(f) == 2 and f[0] == "local":
        f = f[1]
    return f

def main():
    sol, given = sys.argv[1], sys.argv[2]
    img = (sys.argv[3] if len(sys.argv) > 3 else "acl2")
    acl2 = "/opt/acl2r/saved_acl2r" if img == "acl2r" else "/opt/acl2/saved_acl2"
    cert = "/opt/acl2/books/build/cert.pl"
    d = tempfile.mkdtemp(prefix="exp2-")
    shutil.copy(sol, os.path.join(d, "solution.lisp"))
    shutil.copy(os.path.join(given, "defs.lisp"), os.path.join(d, "defs.lisp"))
    for extra in ("defs.acl2", "cert.acl2"):
        p = os.path.join(given, extra)
        if os.path.exists(p): shutil.copy(p, d)
    src = open(os.path.join(d, "solution.lisp")).read()
    code = re.sub(r";[^\n]*", "", src)
    m = BANNED.search(code)
    if m:
        print(f"BANNED: {m.group(0)}"); print(d); sys.exit(2)
    forms = [unlocal(f) for f in parse(tokens(src))]
    if not any(isinstance(f, list) and f[:2] == ["include-book", '"defs"'] for f in forms):
        print('NO-INCLUDE: solution must (include-book "defs")'); print(d); sys.exit(3)
    # every include-book must be "defs" or a community book (:dir :system)
    def includes(x, acc):
        if isinstance(x, list):
            if x and x[0] == "include-book": acc.append(x)
            for y in x: includes(y, acc)
        return acc
    for f in includes(forms, []):
        if f[1:2] == ['"defs"']: continue
        if ":dir" in f and f[f.index(":dir") + 1:f.index(":dir") + 2] == [":system"]: continue
        print("BAD-INCLUDE: only \"defs\" and :dir :system books may be included: " + " ".join(map(str, f[:4])))
        print(d); sys.exit(5)
    # exported theorems: top level, or inside encapsulate/progn (any depth), but never under local
    defined = {}
    def collect(f):
        if not isinstance(f, list) or not f:
            return
        if f[0] == "local":
            return
        if f[0] in ("defthm", "defthmd", "defthm-std") and len(f) >= 3:
            defined.setdefault(f[1], f[2]); return
        if f[0] == "encapsulate":
            for g in f[2:]: collect(g)
        elif f[0] == "progn":
            for g in f[1:]: collect(g)
    for f in parse(tokens(src)):
        collect(f)
    targets = [f for f in parse(tokens(open(os.path.join(given, "targets.lisp")).read()))
               if isinstance(f, list) and len(f) >= 3 and f[0] in ("defthm", "defthmd", "defthm-std")]
    bad = []
    for t in targets:
        name, stmt = t[1], t[2]
        if name not in defined:
            bad.append(f"missing {name}")
        elif defined[name] != stmt:
            bad.append(f"statement of {name} differs from the target")
    if bad:
        print("TARGET-MISMATCH: " + "; ".join(bad)); print(d); sys.exit(4)
    log = os.path.join(d, "check.log")
    with open(log, "w") as fh:
        r = subprocess.run(["perl", cert, "--acl2", acl2, "solution.lisp"], cwd=d, stdout=fh,
                           stderr=subprocess.STDOUT, timeout=7200)
    if r.returncode == 0 and os.path.exists(os.path.join(d, "solution.cert")):
        print(f"CERTIFIED with {os.path.basename(acl2)}; targets matched: "
              + ", ".join(t[1] for t in targets)); print(d); sys.exit(0)
    print("FAILED: did not certify; see " + log); print(d); sys.exit(1)

if __name__ == "__main__":
    main()
