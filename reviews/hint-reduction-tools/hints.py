"""Locate and remove :hints (and hint sub-keys) in an ACL2 source file, by text spans."""
import sys, json, re

def tokens(s):
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c.isspace(): i += 1; continue
        if c == ';':
            while i < n and s[i] != '\n': i += 1
            continue
        if s.startswith('#|', i):
            d = 1; i += 2
            while i < n and d:
                if s.startswith('#|', i): d += 1; i += 2
                elif s.startswith('|#', i): d -= 1; i += 2
                else: i += 1
            continue
        if c in '()':
            yield (c, i, i + 1); i += 1; continue
        if c in "'`": yield ('q', i, i + 1); i += 1; continue
        if c == ',':
            j = i + 2 if s.startswith(',@', i) else i + 1
            yield ('q', i, j); i = j; continue
        if c == '"':
            j = i + 1
            while s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            yield ('atom', i, j + 1); i = j + 1; continue
        j = i
        if s.startswith('#\\', j): j += 3
        while j < n and not s[j].isspace() and s[j] not in '();"':
            if s[j] == '|':
                j += 1
                while s[j] != '|': j += 1
            j += 1
        yield ('atom', i, j); i = j

def sexp_end(toks, k):
    """index (exclusive) of tokens forming the sexp starting at toks[k]; returns token index after it"""
    t = toks[k][0]
    if t == 'q': return sexp_end(toks, k + 1)
    if t == 'atom': return k + 1
    assert t == '('
    d = 0
    while True:
        if toks[k][0] == '(': d += 1
        elif toks[k][0] == ')':
            d -= 1
            if d == 0: return k + 1
        k += 1

def find(s, key=':hints'):
    toks = list(tokens(s))
    out = []
    for k, (t, a, b) in enumerate(toks):
        if t == 'atom' and s[a:b].lower() == key:
            e = sexp_end(toks, k + 1)
            out.append((a, toks[e - 1][2]))
    return out

def remove(s, spans):
    for a, b in sorted(spans, reverse=True):
        a2 = a
        while a2 > 0 and s[a2 - 1] in ' \t\n': a2 -= 1
        s = s[:a2] + s[b:]
    return s

def event_name(s, pos):
    """name of the top-level-ish event containing pos (nearest preceding '(defthm|defun... name')"""
    m = None
    for m in re.finditer(r'\((?:defthmd?|defun-sk|defun|defrule|defchoose)\s+([^\s()]+)', s[:pos], re.I):
        pass
    return m.group(1) if m else '?'

if __name__ == '__main__':
    cmd, path = sys.argv[1], sys.argv[2]
    s = open(path).read()
    spans = find(s)
    if cmd == 'list':
        for i, (a, b) in enumerate(spans):
            print(i, event_name(s, a), s.count('\n', 0, a) + 1, ' '.join(s[a:b].split())[:100])
    elif cmd == 'variants':  # write one file per removable hint into outdir/i/solution.lisp
        import os
        out = sys.argv[3]
        for i, sp in enumerate(spans):
            os.makedirs(f'{out}/{i}', exist_ok=True)
            open(f'{out}/{i}/solution.lisp', 'w').write(remove(s, [sp]))
        print(len(spans))
    elif cmd == 'remove':  # remove the hints with given indices; write to stdout
        idx = {int(x) for x in sys.argv[3].split(',') if x}
        sys.stdout.write(remove(s, [sp for i, sp in enumerate(spans) if i in idx]))

def subkeys(s):
    """spans of (key value) pairs inside hint goal-specs, plus individual :use instances"""
    toks = list(tokens(s)); out = []
    for a, b in find(s):
        for k, (t, x, y) in enumerate(toks):
            if x < a or y > b or t != 'atom': continue
            key = s[x:y].lower()
            if key in (':in-theory', ':induct', ':expand', ':do-not-induct', ':use', ':cases', ':do-not'):
                e = sexp_end(toks, k + 1)
                out.append((x, toks[e - 1][2], key))
    return out

if __name__ == '__main__' and sys.argv[1] == 'subvariants':
    import os
    s = open(sys.argv[2]).read(); out = sys.argv[3]
    for i, (a, b, key) in enumerate(subkeys(s)):
        os.makedirs(f'{out}/{i}', exist_ok=True)
        open(f'{out}/{i}/solution.lisp', 'w').write(remove(s, [(a, b)]))
        print(i, event_name(s, a), key)

if __name__ == '__main__' and sys.argv[1] == 'subremove':
    s = open(sys.argv[2]).read()
    idx = {int(x) for x in sys.argv[3].split(',') if x}
    sp = [(a, b) for i, (a, b, k) in enumerate(subkeys(s)) if i in idx]
    sys.stdout.write(remove(s, sp))

def instances(s):
    """spans of individual elements inside :use lists that have 2+ elements"""
    toks = list(tokens(s)); out = []
    for a, b in find(s):
        for k, (t, x, y) in enumerate(toks):
            if x < a or y > b or t != 'atom' or s[x:y].lower() != ':use': continue
            if toks[k + 1][0] != '(' : continue
            j = k + 2; elems = []
            # is it a single (:instance ...) form rather than a list?
            if toks[j][0] == 'atom' and s[toks[j][1]:toks[j][2]].lower().startswith(':'): continue
            while toks[j][0] != ')':
                e = sexp_end(toks, j); elems.append((toks[j][1], toks[e - 1][2])); j = e
            if len(elems) > 1: out += elems
    return out

if __name__ == '__main__' and sys.argv[1] in ('instvariants', 'instremove'):
    import os
    s = open(sys.argv[2]).read(); ins = instances(s)
    if sys.argv[1] == 'instvariants':
        out = sys.argv[3]
        for i, (a, b) in enumerate(ins):
            os.makedirs(f'{out}/{i}', exist_ok=True)
            open(f'{out}/{i}/solution.lisp', 'w').write(remove(s, [(a, b)]))
            print(i, event_name(s, a), ' '.join(s[a:b].split())[:70])
    else:
        idx = {int(x) for x in sys.argv[3].split(',') if x}
        sys.stdout.write(remove(s, [sp for i, sp in enumerate(ins) if i in idx]))
