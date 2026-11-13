# Checks that every non-local form of defs.lisp occurs verbatim (whitespace/comments normalized)
# in master books/projects/linear/vectors.lisp, and every LOCAL form's body occurs in
# master books/projects/linear/support/vectors.lisp.
# usage: python3 -I check-verbatim.py defs.lisp vectors.lisp support-vectors.lisp
import sys, re, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from forms import forms
norm=lambda t: re.sub(r'\s+',' ',re.sub(r';[^\n]*','',t)).strip()
main={norm(t) for l,k,n,t in forms(sys.argv[2])}
sup={norm(t) for l,k,n,t in forms(sys.argv[3])}
bad=0
for l,k,n,t in forms(sys.argv[1]):
    if k in ('in-package','include-book'): continue
    if k=='local':
        inner=norm(t)[len('(local'):-1].strip()
        m=re.match(r'\((defthmd|defthm|defun|defund) ',inner)
        alt='(local-'+inner[1:] if m else None
        if inner not in sup and alt not in sup: print('LOCAL NOT IN SUPPORT', l, n); bad+=1
    elif norm(t) not in main: print('NOT VERBATIM', l, k, n); bad+=1
print('OK' if bad==0 else f'{bad} problems')
