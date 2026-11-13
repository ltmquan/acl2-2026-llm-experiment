#!/usr/bin/env python3
"""Make the model-facing definitions file (no admission lemmas) from a verified defs.lisp.

Usage: python3 -I make-prompt-defs.py <given-dir>
Writes <given-dir>/prompt/defs.lisp and <given-dir>/prompt/defs.acl2.

Text-level transformation, preserving every definition byte-for-byte:
  * drop every top-level (local ...) form;
  * inside top-level encapsulates, drop (local (defthm|defthmd|defrule|defruled|defrulel|in-theory|include-book ...))
    but keep local definitions (encapsulate witnesses);
  * wrap every remaining top-level event except in-package / include-book / in-theory / defmacro / defconst /
    deflabel in (skip-proofs ...);
  * drop full-line comments (they can describe proof ideas).
defs.acl2 = the directory's cert.acl2 (if any) + a cert-flags line allowing skip-proofs in this one book.
"""
import os, re, sys

def spans(s, start, end):
    """Top-level form spans [a,b) within s[start:end]; skips comments/whitespace."""
    out, i = [], start
    while i < end:
        c = s[i]
        if c == ";":
            j = s.find("\n", i); i = end if j < 0 or j > end else j
        elif s.startswith("#|", i):
            i = s.index("|#", i) + 2
        elif c.isspace():
            i += 1
        elif c == "(":
            a, depth = i, 0
            while True:
                c = s[i]
                if c == ";":
                    i = s.find("\n", i); continue
                if s.startswith("#|", i):
                    i = s.index("|#", i) + 2; continue
                if s.startswith("#\\", i):
                    i += 3; continue
                if c == '"':
                    i += 1
                    while s[i] != '"':
                        i += 2 if s[i] == "\\" else 1
                    i += 1; continue
                if c == "|":
                    i = s.index("|", i + 1) + 1; continue
                if c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                    if depth == 0:
                        i += 1; break
                i += 1
            out.append((a, i))
        else:  # atom at top level (rare)
            a = i
            while i < end and not s[i].isspace() and s[i] not in "()":
                i += 1
            out.append((a, i))
    return out

def head(s, a, b, k=2):
    return re.findall(r"[^\s()]+", s[a:min(b, a + 200)])[:k]

KEEP_PLAIN = {"in-package", "include-book", "in-theory", "defmacro", "defconst", "deflabel", "set-ignore-ok",
              "set-irrelevant-formals-ok", "set-well-founded-relation", "table", "add-macro-alias",
              "set-default-hints", "defxdoc"}
HINT_KEYS = (":hints", ":guard-hints", ":measure-hints")

def strip_hints(t):
    """Remove ':hints <form>' / ':guard-hints <form>' pairs (they do not affect the logic)."""
    out, i, low = [], 0, t.lower()
    while True:
        m = re.search(r"(?<![\w-])(" + "|".join(re.escape(k) for k in HINT_KEYS) + r")(?![\w-])", low[i:])
        if not m:
            out.append(t[i:]); break
        a = i + m.start(); j = i + m.end()
        while t[j].isspace(): j += 1
        if t[j] == "(":
            b = j + _match_len(t, j)
        else:
            b = j
            while b < len(t) and not t[b].isspace() and t[b] not in "()": b += 1
        out.append(t[i:a]); i = b
    return "".join(out)

def _match_len(t, j):
    depth = 0; k = j
    while True:
        c = t[k]
        if c == '"':
            k += 1
            while t[k] != '"': k += 2 if t[k] == "\\" else 1
        elif c == ";":
            k = t.find("\n", k)
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0: return k + 1 - j
        k += 1
LOCAL_DROP = {"defthm", "defthmd", "defrule", "defruled", "defrulel", "in-theory", "encapsulate", "defruledl"}

def strip_comment_lines(t):
    return "\n".join(l for l in t.splitlines() if not l.lstrip().startswith(";"))

def transform(s):
    out = []
    for a, b in spans(s, 0, len(s)):
        h = head(s, a, b)
        kind = h[0].lstrip("(").lower() if h else ""
        if kind == "local":
            inner_kind = (head(s, a, b, 3)[1:2] or [""])[0].lstrip("(").lower()
            if inner_kind == "include-book":
                out.append(s[a:b])
            continue
        text = s[a:b]
        if kind == "encapsulate":
            # drop local lemmas inside, keep local definitions
            inner = spans(s, a + 1, b - 1)
            keep = [(x, y) for (x, y) in inner]
            pieces, last = [], a
            for x, y in inner:
                hh = [t.lstrip("(").lower() for t in re.findall(r"[^\s()]+|\(", s[x:min(y, x + 120)])]
                hh = [t for t in hh if t and t != "("]
                if hh[:1] == ["local"] and len(hh) > 1 and hh[1] in LOCAL_DROP:
                    pieces.append(s[last:x]); last = y
            pieces.append(s[last:b])
            text = "".join(pieces)
        text = strip_comment_lines(text)
        if kind in KEEP_PLAIN:
            out.append(text)
        else:
            out.append("(skip-proofs\n" + strip_hints(text) + ")")
    return "\n\n".join(out) + "\n"

def main():
    g = sys.argv[1]
    s = open(os.path.join(g, "defs.lisp")).read()
    os.makedirs(os.path.join(g, "prompt"), exist_ok=True)
    open(os.path.join(g, "prompt", "defs.lisp"), "w").write(transform(s))
    acl2 = ""
    if os.path.exists(os.path.join(g, "cert.acl2")):
        acl2 = open(os.path.join(g, "cert.acl2")).read().rstrip() + "\n"
    # directory-wide: books that include defs.lisp (which uses skip-proofs) must also permit it
    open(os.path.join(g, "prompt", "cert.acl2"), "w").write(acl2 + "; cert-flags: ? t :skip-proofs-okp t\n")
    p = os.path.join(g, "prompt", "defs.acl2")
    if os.path.exists(p): os.remove(p)
    print(g, "->", os.path.getsize(os.path.join(g, "prompt", "defs.lisp")), "bytes")

if __name__ == "__main__":
    main()
