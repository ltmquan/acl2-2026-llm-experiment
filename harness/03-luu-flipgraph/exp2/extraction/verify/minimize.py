import sys, subprocess, os
sys.path.insert(0, '/home/user/acl2-exp/exp2/given/luu-flipgraph/verify')
from forms import forms, head
os.chdir(os.path.dirname(os.path.abspath(__file__)))
text = open('defs.lisp').read()
def spans(t):
    # (start,end) of top-level local forms other than include-books
    res = []; i = 0
    for ln, f in forms(t):
        s = t.index(f, i); i = s + len(f)
        if f.startswith('(local') and 'include-book' not in f[:30]:
            res.append((s, i))
    return res
def ok(t):
    open('try.lisp', 'w').write(t)
    for e in ('try.cert',):
        if os.path.exists(e): os.remove(e)
    r = subprocess.run(['/opt/acl2/books/build/cert.pl', '--acl2', '/opt/acl2/saved_acl2', 'try.lisp'], capture_output=True)
    return os.path.exists('try.cert')
k = len(spans(text)) - 1
while k >= 0:
    sp = spans(text)
    s, e = sp[k]
    cand = text[:s] + text[e:]
    if ok(cand):
        print("REMOVED", text[s:e][:80].replace('\n', ' ')); text = cand
    else:
        print("KEPT", text[s:e][:80].replace('\n', ' '))
    sys.stdout.flush()
    k -= 1
open('defs.min.lisp', 'w').write(text)
