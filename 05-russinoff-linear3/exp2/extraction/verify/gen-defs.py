import re
import sys,json
sys.path.insert(0,sys.path[0])
from forms import forms
M=forms('src/vectors.lisp'); S=forms('src/support_vectors.lisp')
EXCL={'vindepp-sk','vdepp-sk','vbasis-mat','wdepp','wdep-coeffs','wcoords','windepp-sk','wdepp-sk','wbasisp','wbasis-mat','wunspanned','extend-to-wbasis','nth-vcomb'}
DEFK=('defun','defund','defun-sk','defchoose','encapsulate')
kept=[(l,k,n,t) for (l,k,n,t) in M if (k in DEFK and n not in EXCL) or k=='in-theory']
keptnames={n for (l,k,n,t) in kept if k in DEFK}
# candidate lemmas from support: lines <998 and 3630..3750
drop=set(json.load(open(sys.argv[1]))) if len(sys.argv)>1 else set()
cands={}  # after-def-name -> list
cur=None; idx=0; order=[]
for (l,k,n,t) in S:
    if k in DEFK and n in keptnames: cur=n; continue
    if not ((l<998) or (1600<=l<1750) or (3586<=l<=3750)): continue
    if k in ('in-package','include-book'): continue
    if k in DEFK and n not in keptnames and k not in ('defun',): continue
    key=f"S{l}"
    order.append(key)
    if key in drop: continue
    cands.setdefault(cur,[]).append((key,t))
out=['(in-package "DM")','',
 ';; Authors\' definitions from ACL2 master books/projects/linear/vectors.lisp (Part III).',
 ';; LOCAL events are proof support copied from master books/projects/linear/support/vectors.lisp;',
 ';; they are needed only to admit the lin encapsulate (c*w0), sbasis0-aux (termination hint) and the',
 ';; sbasis1 encapsulate (slistnp-sbasis0, flistnp-scoords0, sbasis0-spans, vindepp-sbasis0).',
 ';; Each event is preceded by its source location.  LOCAL events are not exported.','',
 '(include-book "projects/linear/reduction" :dir :system)',
'']
def localize(t):
    m=re.match(r'\(local-(defthmd|defthm|defun|defund) ',t)
    if m: return '(local\n ('+t[len('(local-'):]+')'
    if t.startswith('(local'): return t
    return '(local\n '+t+')'
for (l,k,n,t) in kept:
    out.append(f';; vectors.lisp:{l}')
    out.append(t); out.append('')
    if k in DEFK and n in cands:
        for key,lt in cands[n]:
            out.append(f';; support/vectors.lisp:{key[1:]}')
            out.append(localize(lt)); out.append('')
open('defs.lisp','w').write('\n'.join(out)+'\n')
json.dump(order,open('order.json','w'))
print(len(order),'candidates')
