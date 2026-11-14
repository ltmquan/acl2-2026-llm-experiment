#!/usr/bin/env python3
"""Static checks for fw-definductive-exec (run with python3 -I).

Usage: check-exec.py <dir> <books-definductive.lisp>

Prints lines
  BANNED <file> <match>
  R1S PASS | R1S FAIL <reason>      (/work/definductive.lisp exists and is a modified copy of the books' file)
  R1INFO <text>                     (diff size; other .lisp files in /work)
  R3S PASS | R3S FAIL <reason>      (exec-tests.lisp contains (i)-(v))
and writes <dir>/grade-h2.lisp: world checks (p-exec-correct form, booleanp-of-p-exec, executability) for every
:exec definition of exec-tests.lisp that is not under must-fail.
"""
import difflib, os, re, sys

BANNED = (r"skip-proofs|defaxiom|defttag|set-ld-redefinition-action|skip-proofs-okp|:ttags|set-skip-proofs|"
          r"trust-tag|define-trusted-clause-processor|defun-unsound|sys-call|reset-prehistory|\bredef\b|set-cbd|"
          r"progn!|defattach-system|set-raw-mode|\bdefstobj\b.*:congruent-to")

# --- tokenizer / parser copied from next/graders/check-prove.py ---------------------------------------
def tokens(s):
    s = re.sub(r"#\|.*?\|#", " ", s, flags=re.S)
    out, i = [], 0
    while i < len(s):
        c = s[i]
        if c == ";":
            j = s.find("\n", i); i = len(s) if j < 0 else j
        elif c.isspace():
            i += 1
        elif c in "()'`,":
            out.append(c); i += 1
        elif c == '"':
            j = i + 1
            while j < len(s) and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append(s[i:j + 1]); i = j + 1
        elif c == "|":
            j = s.find("|", i + 1); out.append(s[i:j + 1]); i = j + 1
        else:
            j = i
            while j < len(s) and not s[j].isspace() and s[j] not in "();\"'`,":
                j += 1
            out.append(s[i:j].lower()); i = j
    return out

def parse(toks):
    def rd(i):
        t = toks[i]
        if t == "(":
            lst, i = [], i + 1
            while toks[i] != ")":
                x, i = rd(i); lst.append(x)
            return lst, i + 1
        if t in ("'", "`", ","):
            x, i = rd(i + 1); return [{"'": "quote", "`": "quasiquote", ",": "unquote"}[t], x], i
        return t, i + 1
    forms, i = [], 0
    while i < len(toks):
        f, i = rd(i); forms.append(f)
    return forms
# ------------------------------------------------------------------------------------------------------

def strip_pkg(x):
    if isinstance(x, str):
        return re.sub(r"^acl2::", "", x)
    return [strip_pkg(y) for y in x]

def subforms(x):
    if isinstance(x, list):
        yield x
        for y in x:
            yield from subforms(y)

def is_var(x):
    return isinstance(x, str) and re.match(r"^[a-z_*+\-/<>=!?%&$^~.][^\s]*$", x) and x not in ("t", "nil") \
        and not x.startswith(":") and not re.match(r"^[-+]?\d", x)

def kw(f, k):
    i = 2
    while i + 1 < len(f):
        if f[i] == k:
            return f[i + 1]
        i += 2
    return None

def calls_in(forms):
    """(call, under_must_fail) for every definductive form."""
    out = []
    def walk(f, mf):
        if not isinstance(f, list) or not f:
            return
        if f[0] == "definductive":
            out.append((f, mf)); return
        for g in f[1:] if isinstance(f[0], str) else f:
            walk(g, mf or f[0] == "must-fail")
    for f in forms:
        walk(f, False)
    return out

def preds_of(c):
    p = kw(c, ":preds")
    return {q[0]: q[1:] for q in p if isinstance(q, list) and q and isinstance(q[0], str)} if isinstance(p, list) else {}

def rules_of(c):
    r = kw(c, ":irules")
    return [x for x in r if isinstance(x, list) and len(x) == 3 and isinstance(x[1], list)] if isinstance(r, list) else []

def exec_entries(c):
    e = kw(c, ":exec")
    out = {}
    if isinstance(e, list):
        for x in e:
            if isinstance(x, list) and x and isinstance(x[0], str):
                nm = kw([None, None] + x[1:], ":name")
                out[x[0]] = nm
    return out

def sccs(preds, rules):
    deps = {p: set() for p in preds}
    for _, prems, concl in rules:
        if isinstance(concl, list) and concl and concl[0] in preds:
            for pr in prems:
                if isinstance(pr, list) and pr and isinstance(pr[0], str) and pr[0] in preds:
                    deps[concl[0]].add(pr[0])
    def reach(a):
        seen, todo = set(), [a]
        while todo:
            x = todo.pop()
            for y in deps.get(x, ()):
                if y not in seen:
                    seen.add(y); todo.append(y)
        return seen
    r = {p: reach(p) for p in preds}
    comps = []
    for p in preds:
        comp = frozenset([p] + [q for q in preds if q != p and q in r[p] and p in r[q]])
        if comp not in comps:
            comps.append(comp)
    return comps

def main():
    d, books_file = sys.argv[1], sys.argv[2]
    for root, _, files in os.walk(d):
        for fn in files:
            if fn.endswith((".lisp", ".lsp", ".acl2")) and not fn.startswith(("grade-", "grader-")):
                src = open(os.path.join(root, fn), errors="replace").read()
                code = re.sub(r";[^\n]*", "", re.sub(r"#\|.*?\|#", " ", src, flags=re.S))
                for m in re.finditer(BANNED, code, re.I):
                    print(f"BANNED {os.path.relpath(os.path.join(root, fn), d)} {m.group(0)}")

    # ---------------- R1
    mine = os.path.join(d, "definductive.lisp")
    if not os.path.exists(mine):
        print("R1S FAIL /work/definductive.lisp is missing")
    else:
        a = open(books_file).read().splitlines()
        b = open(mine, errors="replace").read().splitlines()
        sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
        kept = sum(bl.size for bl in sm.get_matching_blocks())
        frac = kept / max(1, len(a))
        print(f"R1INFO definductive.lisp: {len(b)} lines; {kept} of the books' {len(a)} lines kept ({frac:.0%}); "
              f"{len(b) - kept} lines added or changed")
        others = sorted(f for f in os.listdir(d) if f.endswith(".lisp") and f not in ("definductive.lisp", "exec-tests.lisp")
                        and not f.startswith(("grade-", "grader-")))
        print("R1INFO other .lisp files in /work: " + (" ".join(others) if others else "none"))
        if not re.search(r"\(\s*defmacro\s+definductive\b", open(mine, errors="replace").read(), re.I):
            print("R1S FAIL /work/definductive.lisp does not define the macro definductive")
        elif frac < 0.5:
            print(f"R1S FAIL /work/definductive.lisp keeps only {frac:.0%} of the books' file: not a modified copy")
        else:
            print("R1S PASS")

    # ---------------- R3 static
    ex = os.path.join(d, "exec-tests.lisp")
    h2 = ['; Generated by check-exec.py from the model\'s exec-tests.lisp (fw-definductive-exec, informative check H2).',
          '(in-package "ACL2")', '(include-book "exec-tests")', '(include-book "grader-utils")', '']
    if not os.path.exists(ex):
        print("R3S FAIL /work/exec-tests.lisp is missing")
        h2.append('(grader-assert h2-none nil "exec-tests.lisp is missing")')
    else:
        try:
            forms = strip_pkg(parse(tokens(open(ex, errors="replace").read())))
        except Exception as e:
            forms = None
            print(f"R3S FAIL exec-tests.lisp does not parse ({e})")
            h2.append('(grader-assert h2-none nil "exec-tests.lisp does not parse")')
        if forms is not None:
            bad = []
            cs = calls_in(forms)
            good = [c for c, mf in cs if not mf and kw(c, ":exec") is not None]
            # (i) even/odd
            def ok_i(c):
                pr, rs = preds_of(c), rules_of(c)
                if not {"even", "odd"} <= set(pr) or not {"even", "odd"} <= set(exec_entries(c)):
                    return False
                z = any(r[2] == ["even", "0"] for r in rs)
                def step(concl_p, prem_p):
                    for _, prems, concl in rs:
                        if (isinstance(concl, list) and len(concl) == 2 and concl[0] == concl_p
                                and isinstance(concl[1], list) and concl[1][:1] == ["1+"] and len(concl[1]) == 2
                                and is_var(concl[1][1])):
                            v = concl[1][1]
                            if ["natp", v] in prems and [prem_p, v] in prems and \
                                    prems.index(["natp", v]) < prems.index([prem_p, v]):
                                return True
                    return False
                return z and step("odd", "even") and step("even", "odd")
            if not any(ok_i(c) for c in good):
                bad.append("(i): no :exec call with even/odd rules (even 0), (odd (1+ n)) <- (natp n) (even n), "
                           "(even (1+ n)) <- (natp n) (odd n)")
            # (ii) naturals plus finitely branching trees of naturals
            def ok_ii(c):
                pr, rs = preds_of(c), rules_of(c)
                if len(pr) < 3 or set(exec_entries(c)) != set(pr):
                    return False
                cons = any(isinstance(r[2], list) and any(isinstance(t, list) and t[:1] == ["cons"] for t in r[2][1:])
                           for r in rs)
                return cons and any(len(s) >= 2 for s in sccs(pr, rs)) and any(len(s) == 1 for s in sccs(pr, rs))
            if not any(ok_ii(c) for c in good):
                bad.append("(ii): no :exec call with naturals plus a clique of trees/lists (>= 3 predicates, a "
                           "singleton clique and a mutual clique, conclusions using cons)")
            # (iii) >= 3 predicates in one clique
            if not any(any(len(s) >= 3 for s in sccs(preds_of(c), rules_of(c))) and set(exec_entries(c)) == set(preds_of(c))
                       for c in good):
                bad.append("(iii): no :exec call with a clique of at least three predicates")
            # (iv) must-fail on refl-trans closure, no binding for the middle variable
            def ok_iv(c):
                if kw(c, ":exec") is None:
                    return False
                binds = kw(c, ":exec-binds") or []
                for rname, prems, concl in rules_of(c):
                    if isinstance(concl, list) and len(concl) == 3 and all(is_var(v) for v in concl[1:]):
                        p, x, z = concl
                        for pr1 in prems:
                            for pr2 in prems:
                                if (isinstance(pr1, list) and isinstance(pr2, list) and len(pr1) == 3 and len(pr2) == 3
                                        and pr1[0] == p and pr2[0] == p and pr1[1] == x and pr2[2] == z
                                        and pr1[2] == pr2[1] and is_var(pr1[2]) and pr1[2] not in (x, z)):
                                    y = pr1[2]
                                    entry = [b for b in binds if isinstance(b, list) and b[:1] == [rname]]
                                    if not any(isinstance(vb, list) and vb[:1] == [y] for e in entry for vb in e[1:]):
                                        return True
                return False
            if not any(ok_iv(c) for c, mf in cs if mf):
                bad.append("(iv): no must-fail on a transitivity rule (r x y) (r y z) => (r x z) with :exec and "
                           "no :exec-binds for y")
            # (v) assert-event on each p-exec
            asserted = set()
            for f in forms:
                for l in subforms(f):
                    if l and l[0] == "assert-event":
                        for g in subforms(l):
                            if g and isinstance(g[0], str):
                                asserted.add(g[0])
            missing = []
            for c in good:
                for p, nm in exec_entries(c).items():
                    if nm is None or nm not in asserted:
                        missing.append(str(nm or p))
            if not good:
                bad.append("(v): no :exec definitions")
            elif missing:
                bad.append("(v): no assert-event evaluating " + " ".join(missing))
            print("R3S " + ("PASS" if not bad else "FAIL " + "; ".join(bad)))
            # ---------------- H2 world checks
            k = 0
            for c in good:
                pr = preds_of(c)
                for p, nm in exec_entries(c).items():
                    k += 1
                    if nm is None or p not in pr:
                        h2.append(f'(grader-assert h2-{k}-entry nil "the :exec entry for {p} has no :name or names no predicate")')
                        continue
                    fs = " ".join(pr[p])
                    h2.append(f"(grader-formula h2-{k}-{nm}-correct {nm}-correct (iff ({nm} {fs}) ({p} {fs})))")
                    h2.append(f"(grader-formula h2-{k}-{nm}-booleanp booleanp-of-{nm} (booleanp ({nm} {fs})))")
                    h2.append(f"(grader-assert h2-{k}-{nm}-formals (equal (grader-formals '{nm} (w state)) '({fs})) "
                              f"\"{nm} does not have the formals of {p}\")")
                    h2.append(f"(grader-assert h2-{k}-{nm}-clean (null (grader-exec-clean '{nm} (w state))) "
                              f"\"{nm} reaches a defun-sk predicate, witness, defchoose or constrained function\")")
            if k == 0:
                h2.append('(grader-assert h2-none nil "no :exec definitions in exec-tests.lisp")')
    h2.append("")
    h2.append("(grader-final)")
    open(os.path.join(d, "grade-h2.lisp"), "w").write("\n".join(h2) + "\n")

if __name__ == "__main__":
    main()
