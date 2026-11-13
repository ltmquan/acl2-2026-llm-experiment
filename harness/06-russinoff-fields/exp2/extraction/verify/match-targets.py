# Compare target statements in targets.lisp with those in a solution file, using
# check-exp2.py's own tokenizer/parser (same comparison the checker makes).
import sys, importlib.util
spec = importlib.util.spec_from_file_location("chk", "/home/user/acl2-exp/env/check-exp2.py")
chk = importlib.util.module_from_spec(spec); spec.loader.exec_module(chk)
sol, tgt = sys.argv[1], sys.argv[2]
d = {f[1]: f[2] for f in map(chk.unlocal, chk.parse(chk.tokens(open(sol).read())))
     if isinstance(f, list) and len(f) >= 3 and f[0] in ("defthm", "defthmd")}
ok = True
for t in chk.parse(chk.tokens(open(tgt).read())):
    if isinstance(t, list) and t[0] == "defthm":
        r = "MATCH" if d.get(t[1]) == t[2] else "MISMATCH"; ok &= r == "MATCH"
        print(t[1], r)
sys.exit(0 if ok else 1)
