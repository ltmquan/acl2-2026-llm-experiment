# Split an ACL2 source file into top-level forms (with line numbers).
import sys, re
def forms(text, limit=None):
    i, n, line = 0, len(text), 1
    out = []
    while i < n:
        c = text[i]
        if c == '\n': line += 1; i += 1; continue
        if c.isspace(): i += 1; continue
        if c == ';':
            while i < n and text[i] != '\n': i += 1
            continue
        if text.startswith('#|', i):
            j = text.index('|#', i); line += text.count('\n', i, j); i = j + 2; continue
        if c == '(':
            start, sline, depth = i, line, 0
            while True:
                ch = text[i]
                if ch == '\n': line += 1
                if ch == ';':
                    while text[i] != '\n': i += 1
                    continue
                if ch == '"':
                    i += 1
                    while text[i] != '"':
                        if text[i] == '\\': i += 1
                        if text[i] == '\n': line += 1
                        i += 1
                elif text.startswith('#\\', i):
                    i += 3; continue
                elif text.startswith('#|', i):
                    j = text.index('|#', i); line += text.count('\n', i, j); i = j + 2; continue
                elif ch == '(':
                    depth += 1
                elif ch == ')':
                    depth -= 1
                    if depth == 0:
                        i += 1; break
                i += 1
            out.append((sline, text[start:i]))
            if limit and len(out) >= limit: return out
            continue
        raise Exception("unexpected %r at line %d" % (c, line))
    return out
def head(f):
    toks = re.findall(r"[^\s()]+", f[:200])
    return [t.lower() for t in toks[:2]]
if __name__ == '__main__':
    for ln, f in forms(open(sys.argv[1]).read()):
        print(ln, *head(f))
