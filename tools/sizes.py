#!/usr/bin/env python3
"""Uniform size counts for ACL2 files: lines, definitions, theorems.
definitions = defun defund define defun-sk defun-std defun-nx defchoose defmacro (+ functions named in encapsulate signatures)
theorems    = defthm defthmd defthm-std defrule defruled defrulel defruledl (wherever they occur, incl. local)
Usage: python3 -I sizes.py <file-or-dir>... (dirs: all *.lisp, recursively)"""
import os, re, sys
DEF = re.compile(r"\(\s*(?:[a-z0-9-]+::)?(defun|defund|define|defun-sk|defun-std|defun-nx|defchoose|defmacro)\s", re.I)
THM = re.compile(r"\(\s*(?:[a-z0-9-]+::)?(defthm|defthmd|defthm-std|defrule|defruled|defrulel|defruledl)\s", re.I)
SIG = re.compile(r"\(\s*encapsulate\s*\(\s*((?:\(\s*\(?[^\s()]+[^)]*\)?[^)]*\)\s*)+)\)", re.I)
def strip(s):
    s = re.sub(r"#\|.*?\|#", "", s, flags=re.S)
    return "\n".join(l.split(";")[0] if '"' not in l else l for l in s.splitlines())
def count(paths):
    files = []
    for p in paths:
        if os.path.isdir(p):
            for r, _, fs in os.walk(p):
                files += [os.path.join(r, f) for f in fs if f.endswith(".lisp")]
        else: files.append(p)
    L = D = T = 0
    for f in files:
        s = open(f, errors="replace").read(); L += s.count("\n"); c = strip(s)
        D += len(DEF.findall(c)); T += len(THM.findall(c))
        for m in SIG.finditer(c): D += len(re.findall(r"\(\s*\(\s*[^\s()]+|\(\s*[^\s()]+\s*\(", m.group(1)))
    return len(files), L, D, T
if __name__ == "__main__":
    n, L, D, T = count(sys.argv[1:]); print(f"files={n} lines={L} defs={D} theorems={T}")
