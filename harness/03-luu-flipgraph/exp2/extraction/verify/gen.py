# Generate a draft defs.lisp: the authors' define/defun-sk forms in the
# definitional closure of the targets, verbatim, with "///" sections removed.
import sys, re, os
sys.path.insert(0, os.path.dirname(__file__))
from forms import forms, head
B = sys.argv[1]
FILES = "bits bags scheme tensor mm-tensor entry adequacy matmul-expr algo-completeness scheme-algo".split()
CLOS = set(open(sys.argv[2]).read().lower().split())
out = []
for fn in FILES:
    for ln, f in forms(open(os.path.join(B, fn + ".lisp")).read()):
        h = head(f)
        if h[0] in ("define", "defun-sk", "defun", "defund") and h[1] in CLOS:
            m = re.search(r"\n[ \t]*///[ \t]*\n", f)
            if m:
                f = f[:m.start()].rstrip() + ")"
            out.append(";; %s.lisp:%d\n%s\n" % (fn, ln, f))
            CLOS.discard(h[1])
print("\n".join(out))
print(";; NOT FOUND:", sorted(CLOS), file=sys.stderr)
