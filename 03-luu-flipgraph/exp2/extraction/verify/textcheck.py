# Check every define/defun-sk form in defs.lisp is verbatim the authors' form
# (up to the removed "///" section) and every local lemma copied from the
# authors (comment ";; file:line" directly above) is verbatim too.
import sys, os, re
sys.path.insert(0, os.path.dirname(__file__))
from forms import forms, head
B = sys.argv[2]
src = {f: open(os.path.join(B, f)).read() for f in os.listdir(B) if f.endswith('.lisp')}
t = open(sys.argv[1]).read()
bad = 0; n = 0
for m in re.finditer(r";; ([a-z0-9-]+\.lisp):(\d+)\n(?:\(local\n )?(\((?:define|defun-sk|defrule|defruled) [^\n]*\n)", t):
    fname = m.group(1); start = m.end(3) - len(m.group(3))
    form = [f for ln, f in forms(t[start:], 1)][0]
    body = form[:-1] if head(form)[0] == 'define' else form
    n += 1
    if body not in src[fname]:
        # allow re-indentation of copied /// lemmas
        norm = lambda s: re.sub(r"\s+", " ", s)
        if norm(body) in norm(src[fname]):
            continue
        bad += 1; print("MISMATCH", fname, m.group(2), head(form))
print("checked", n, "forms;", bad, "mismatches")
