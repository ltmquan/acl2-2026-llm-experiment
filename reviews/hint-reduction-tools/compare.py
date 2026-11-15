import sys
sys.path.insert(0, '/tmp/nohints-tools')
from hints import tokens, sexp_end, find, remove
def forms(path):
    s = open(path).read()
    s = remove(s, find(s))
    toks = list(tokens(s)); out = []; k = 0
    while k < len(toks):
        e = sexp_end(toks, k)
        out.append(' '.join(s[toks[k][1]:toks[e-1][2]].split()).lower()); k = e
    return out
a, b = forms(sys.argv[1]), forms(sys.argv[2])
isth = lambda f: not f.startswith('(in-theory')
A = [f for f in a if isth(f)]; B = [f for f in b if isth(f)]
print('original events (excl. in-theory):', len(A), ' new:', len(B))
print('missing from new:', [f[:80] for f in A if f not in B])
print('added in new:', [f[:100] for f in B if f not in A])
print('in-theory events: original', len(a)-len(A), ' new', len(b)-len(B))
print('order of shared events same:', [f for f in A if f in B] == [f for f in B if f in A])
