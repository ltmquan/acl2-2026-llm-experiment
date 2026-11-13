# V3: compare defs/targets against the paper text (whitespace-insensitive, case-insensitive).
import re, sys
d = sys.argv[1]
paper = open(d + "/verify/gamboa-basel-layout.txt").read().splitlines()
def norm(s): return re.sub(r"\s+", "", re.sub(r";[^\n]*", "", s)).lower()
i = next(k for k,l in enumerate(paper) if re.sub(r"\s","",l).startswith("(defunbasel-series("))
p_def = norm("\n".join(paper[i:i+6]))
j = next(k for k,l in enumerate(paper) if re.sub(r"\s","",l)=="(defthmdbasel-series-closed-form-close")
p_thm = norm("\n".join(paper[j+1:j+5]))
defs = open(d + "/defs.lisp").read()
m = defs.index("(defun basel-series")
g_def = norm(defs[m:])
tg = open(d + "/targets.lisp").read()
m = tg.index("(implies")
g_thm = norm(tg[m:])[:-1]                         # drop the defthm's closing paren
print("paper def :", p_def); print("given def :", g_def); print("DEF IDENTICAL:", p_def == g_def)
print("paper thm :", p_thm); print("given thm :", g_thm); print("STMT IDENTICAL:", p_thm == g_thm)
print("paper name line:", re.sub(r"\s", "", paper[j]) + "  (line %d; def at line %d)" % (j+1, i+1))
