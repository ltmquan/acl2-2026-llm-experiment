#!/usr/bin/env python3
"""Exit 0 iff two Lisp files have the same tokens after removing ; and #|...|# comments and whitespace.
Usage: python3 -I check-comments-only.py <a.lisp> <b.lisp>"""
import re, sys
def toks(p):
    s = open(p).read(); s = re.sub(r"#\|.*?\|#", " ", s, flags=re.S); out = []
    for line in s.splitlines():
        code, i, instr = [], 0, False
        while i < len(line):
            c = line[i]
            if c == '"': instr = not instr
            if c == "\\" and instr: code.append(line[i:i+2]); i += 2; continue
            if c == ";" and not instr: break
            code.append(c); i += 1
        out += "".join(code).split()
    return out
a, b = toks(sys.argv[1]), toks(sys.argv[2])
print("IDENTICAL apart from comments and whitespace" if a == b else "DIFFERENT"); sys.exit(0 if a == b else 1)
