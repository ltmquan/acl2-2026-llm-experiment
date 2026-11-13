# Check that v3-main34.lisp embeds Part B of defs.lisp VERBATIM
# (text of defs.lisp from "(defun g-cplxp" to end of file).
# Usage: python3 -I gen-v3-main34.py <given-dir>
import sys
g = sys.argv[1]
d = open(g + '/defs.lisp').read()
partB = d[d.index('(defun g-cplxp'):]
v = open(g + '/verify/v3-main34.lisp').read()
start = v.index('; ---- Part B of defs.lisp, verbatim ----\n') + len('; ---- Part B of defs.lisp, verbatim ----\n')
end = v.index('\n; ---- Equivalence')
print('VERBATIM' if v[start:end] == partB else 'DIFFERENT')
