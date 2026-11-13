#!/usr/bin/env python3
"""Annotate an experiment-2 definitions file with the source location of every form.

Usage: python3 -I annotate-defs.py <defs.lisp> <out.lisp> <label>=<source.lisp> ...

For each top-level form of <defs.lisp> (and each form inside a top-level encapsulate), find the
authors' form it was copied from: first an exact match (same tokens, ignoring comments,
whitespace and case) among all forms of the source files at any nesting depth; then a match with
a "G-" renaming undone; then a form of the same kind and name ("edited copy").  Writes <out.lisp>,
which is <defs.lisp> with comment lines added and nothing else changed:
  ;;; ===== from <label> =====          when the source file changes
  ;;; <label>, lines a-b [(edited copy)] before each form
  ;;; not from the authors' sources       when nothing matches
Run check-comments-only.py afterwards to confirm the output differs from the input only in comments.
"""
import re, sys

def lex(s):
    """tokens with (start offset) ; comments, #|..|#, strings, |sym|, #\\c handled"""
    out, i, n = [], 0, len(s)
    while i < n:
        c = s[i]
        if c == ";":
            j = s.find("\n", i); i = n if j < 0 else j
        elif s.startswith("#|", i):
            i = s.index("|#", i) + 2
        elif c.isspace():
            i += 1
        elif c in "()'`":
            out.append((c, i)); i += 1
        elif c == ",":
            k = 2 if s.startswith(",@", i) else 1; out.append((s[i:i+k], i)); i += k
        elif s.startswith("#\\", i):
            j = i + 3
            while j < n and not s[j].isspace() and s[j] not in "()": j += 1
            out.append((s[i:j], i)); i = j
        elif c == '"':
            j = i + 1
            while s[j] != '"': j += 2 if s[j] == "\\" else 1
            out.append((s[i:j+1], i)); i = j + 1
        elif c == "|":
            j = s.index("|", i + 1); out.append((s[i:j+1], i)); i = j + 1
        else:
            j = i
            while j < n and not s[j].isspace() and s[j] not in "();\"'`,": j += 1
            out.append((s[i:j].lower(), i)); i = j
    return out

def forms(toks, s):
    """list of (start, end, tokens, depth, kind, name) for every parenthesised form"""
    res, stack = [], []
    for k, (t, p) in enumerate(toks):
        if t == "(":
            stack.append(k)
        elif t == ")":
            a = stack.pop()
            body = [x for x, _ in toks[a:k+1]]
            end = p + 1
            res.append((toks[a][1], end, body, len(stack), body[1] if len(body) > 1 else "",
                        body[2] if len(body) > 2 else ""))
    return res

def line_of(s, off): return s.count("\n", 0, off) + 1

def main():
    src_path, out_path = sys.argv[1], sys.argv[2]
    sources = []
    for a in sys.argv[3:]:
        label, path = a.split("=", 1)
        t = open(path, errors="replace").read()
        sources.append((label, t, forms(lex(t), t)))
    s = open(src_path).read()
    toks = lex(s)
    allf = forms(toks, s)
    top = [f for f in allf if f[3] == 0]
    inner = [f for f in allf if f[3] == 1 and any(g[4] == "encapsulate" and g[0] < f[0] < g[1] for g in top)
             and f[4] not in ("local",) or (f[3] == 2 and False)]
    exact = {}
    for label, t, fs in sources:
        for f in fs:
            exact.setdefault(tuple(f[2]), (label, line_of(t, f[0]), line_of(t, f[1] - 1)))
    def ungee(body): return tuple(x[2:] if x.startswith("g-") else x for x in body)
    def find(f):
        body = tuple(f[2])
        if body in exact: return exact[body] + ("",)
        if f[4] == "local" and len(body) > 3:   # (local (X ...)) : look for the inner form
            inner_b = body[2:-1]
            if inner_b in exact: return exact[inner_b] + (" (wrapped in local)",)
        if ungee(body) in exact: return exact[ungee(body)] + (" (renamed with prefix G-)",)
        kind, name = f[4], f[5]
        if kind == "local" and len(body) > 4: kind, name = body[3], body[4]
        if name.startswith("("): return None
        names = {name, name[2:] if name.startswith("g-") else name}
        for label, t, fs in sources:
            for g in fs:
                if g[5] in names and (g[4] == kind or {g[4], kind} <= {"defthm", "defthmd", "local-defthm",
                                                                       "local-defthmd", "defrule", "defruled"}):
                    return (label, line_of(t, g[0]), line_of(t, g[1] - 1), " (edited copy; see notes)")
        return None
    targets = sorted(top + [f for f in allf if f[3] == 1 and any(g[4] == "encapsulate" and g[0] < f[0] < g[1] for g in top)],
                     key=lambda f: f[0])
    ins, last = [], None
    for f in targets:
        if f[3] == 0 and f[4] in ("in-package",): continue
        if f[3] == 0 and f[4] == "encapsulate":
            r = find(f)
            if r is None:   # annotate the parts instead
                continue
        r = find(f)
        bol = s.rfind("\n", 0, f[0]) + 1
        indent = s[bol:f[0]] if s[bol:f[0]].strip() == "" else None
        if indent is None: continue          # form does not start its own line; skip
        if f[3] == 1 and any(g[4] == "encapsulate" and g[0] < f[0] < g[1] and find(g) for g in top):
            continue                         # whole encapsulate already matched
        if r is None:
            lines = [indent + ";;; not from the authors' sources"]
        else:
            label, a, b, note = r
            lines = []
            if label != last and f[3] == 0:
                lines.append(indent + f";;; ===== from {label} =====")
            last = label
            lines.append(indent + f";;; {label}, lines {a}-{b}{note}")
        ins.append((bol, "".join(l + "\n" for l in lines)))
    out, prev = [], 0
    for p, txt in sorted(ins):
        out.append(s[prev:p]); out.append(txt); prev = p
    out.append(s[prev:])
    open(out_path, "w").write("".join(out))
    n_none = sum(1 for _, t in ins if "not from" in t)
    print(f"{out_path}: {len(ins)} annotations, {n_none} not from the authors' sources")

if __name__ == "__main__":
    main()
