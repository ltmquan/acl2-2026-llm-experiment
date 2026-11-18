#!/usr/bin/env python3
"""Split ext/zfc-task-specs-check.lisp into per-task defs.lisp / targets.lisp."""
import re, os
SRC = "/home/user/acl2-exp/ext/zfc-task-specs-check.lisp"
OUT = "/home/user/acl2-exp/next-build/zfc"
txt = open(SRC).read()
head, *secs = re.split(r"\n;;; -+ ", txt)
def forms(s):
    out, i, n = [], 0, len(s)
    while i < n:
        if s[i] == ';':
            i = s.find('\n', i); i = n if i < 0 else i; continue
        if s[i] == '(':
            d, j = 0, i
            while True:
                c = s[j]
                if c == ';' : j = s.find('\n', j); continue
                if c == '"':
                    j += 1
                    while s[j] != '"': j += 2 if s[j] == '\\' else 1
                elif c == '(': d += 1
                elif c == ')':
                    d -= 1
                    if d == 0: break
                j += 1
            out.append(s[i:j+1]); i = j + 1; continue
        i += 1
    return out
INCL = """(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)"""
CERT = '(include-book "projects/set-theory/portcullis" :dir :system)\n; cert_param: (non-acl2r)\n'
letters = "ABCDEFGHIJK"
data = {}
for s in secs:
    L = s[0]; title = s.split("\n", 1)[0][3:].strip()
    fs = forms(s.split("\n", 1)[1])
    defs = [f for f in fs if not f.startswith("(chk ")]
    thms = ["(defthmz " + f[5:] for f in fs if f.startswith("(chk ")]
    data[L] = (title, defs, thms)
for k, L in enumerate(letters):
    title, defs, thms = data[L]
    t = f"T{k+1}"
    d = os.path.join(OUT, f"zfc-{t.lower()}"); os.makedirs(d, exist_ok=True)
    pre = []
    if L == "K":
        for P in "ABC": pre += data[P][1]
    body = "\n\n".join(pre + defs)
    open(os.path.join(d, "defs.lisp"), "w").write(f'(in-package "ZF")\n\n{INCL}\n\n{body}\n')
    open(os.path.join(d, "cert.acl2"), "w").write(CERT)
    open(os.path.join(d, "targets.lisp"), "w").write("\n\n".join(thms) + "\n")
    open(os.path.join(d, "title.txt"), "w").write(title + "\n")
    print(t, title, len(defs), "defs", len(thms), "targets")
