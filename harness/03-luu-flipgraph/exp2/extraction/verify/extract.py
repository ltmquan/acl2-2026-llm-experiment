# Print named theorems from an authors' file (top level or inside a define's
# /// section), each wrapped in (local ...), verbatim otherwise.
import sys, re, os
sys.path.insert(0, os.path.dirname(__file__))
from forms import forms, head
raw = sys.argv[1] == '-raw'
args = sys.argv[2:] if raw else sys.argv[1:]
src, names = args[0], [n.lower() for n in args[1:]]
text = open(src).read()
found = {}
def scan(t, base):
    for ln, f in forms(t):
        h = head(f)
        if h[0] == 'local':
            inner = f[len('(local'):-1]
            for ln2, g in forms(inner):
                found.setdefault(head(g)[1], (base + ln - 1 + ln2 - 1, g))
        elif h[0] in ('define',):
            m = re.search(r"\n[ \t]*///[ \t]*\n", f)
            if m:
                scan(f[m.end():-1], base + ln - 1 + f[:m.end()].count('\n'))
        else:
            found.setdefault(h[1], (base + ln - 1, f))
scan(text, 1)
for n in names:
    ln, f = found[n]
    if raw:
        print(";; %s:%d\n%s\n" % (os.path.basename(src), ln, f))
    else:
        print(";; %s:%d\n(local\n %s)\n" % (os.path.basename(src), ln, f))
