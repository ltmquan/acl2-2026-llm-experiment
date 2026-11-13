# Textual (token-level, comments ignored, case-insensitive) comparison of every
# definition in defs.lisp with the authors' definition of the same name.
# Part B names are mapped back by stripping the G- prefix.
# Usage: python3 -I compare-defs.py <given-dir> <authors-dir>
import sys, importlib.util
spec = importlib.util.spec_from_file_location('chk', '/home/user/acl2-exp/env/check-exp2.py')
chk = importlib.util.module_from_spec(spec); spec.loader.exec_module(chk)
g, a = sys.argv[1], sys.argv[2]
def forms(p): return [chk.unlocal(f) for f in chk.parse(chk.tokens(open(p).read()))]
A = {}
filesA = ['00-complex-vectors', '01-euler-identities', '02-roots-of-unity', '05-torque-sign-correction']
for fn in filesA:
    for f in forms(f'{a}/{fn}.lisp'):
        if isinstance(f, list) and f[0] == 'defun': A[f[1]] = f
        if isinstance(f, list) and f[0] == 'encapsulate': A['<encapsulate>'] = f
B = {}
for f in forms(f'{a}/06-generic-omega-collapse-acl2r.lisp'):
    if isinstance(f, list) and f[0] == 'defun': B[f[1]] = f
def unprefix(x):
    if isinstance(x, list): return [unprefix(y) for y in x]
    return x[2:] if isinstance(x, str) and x.startswith('g-') else x
ok = True
for f in forms(f'{g}/defs.lisp'):
    if not isinstance(f, list): continue
    if f[0] == 'encapsulate':
        r = 'IDENTICAL' if f == A['<encapsulate>'] else 'DIFFERENT'; print('encapsulate cosine/sine:', r)
    elif f[0] == 'defun':
        n = f[1]
        if n.startswith('g-'):
            u = unprefix(f); src = B.get(u[1])
            r = 'IDENTICAL modulo G- renaming' if u == src else f'DIFFERENT authors={src} given={f}'
        else:
            r = 'IDENTICAL' if f == A.get(n) else 'DIFFERENT'
        print(f'{n}: {r}')
        if r.startswith('DIFFERENT'): ok = ok and n == 'g-gamma-val'
    elif f[0] in ('defthm', 'verify-guards'):
        print(f'[{f[0]} {f[1]}] (local admission scaffolding)' if f[0]=='defthm' else f'[verify-guards {f[1]}]')
print('ALL IDENTICAL except g-gamma-val (intended)' if ok else 'UNEXPECTED DIFFERENCES')
