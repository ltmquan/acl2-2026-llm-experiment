#!/usr/bin/env python3
"""Static checks for tool-definductive (run with python3 -I).

Usage: check-examples.py <dir>      (dir: copy of the model's /work)

Prints lines
  BANNED <file> <match>             (any banned event in a .lisp/.lsp/.acl2 file)
  R2S PASS | R2S FAIL <reason>      (examples.lisp: include of "definductive", defstub r, the four paper calls)
  R3S PASS | R3S FAIL <reason>      (examples.lisp: the hint parts the paper shows, Section 5)
  R4S PASS | R4S FAIL <reason>      (examples.lisp: must-fail on no-proof-trees and on and/or/not/implies premises)
Exit 0 always (grade.sh interprets the lines).
"""
import os, re, sys

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

def P(s):
    return parse(tokens(s))[0]

def strip_pkg(x):
    if isinstance(x, str):
        return re.sub(r"^acl2::", "", x)
    return [strip_pkg(y) for y in x]

def subforms(x):
    """All lists in x (x itself included), depth first."""
    if isinstance(x, list):
        yield x
        for y in x:
            yield from subforms(y)

def atoms(x):
    if isinstance(x, list):
        for y in x:
            yield from atoms(y)
    else:
        yield x

def contains(x, y):
    return any(z == y for z in subforms(x)) if isinstance(y, list) else y in set(atoms(x))

def kwarg(form, kw):
    """Values following keyword kw anywhere in the form."""
    out = []
    for l in subforms(form):
        for i in range(len(l) - 1):
            if l[i] == kw:
                out.append(l[i + 1])
    return out

PAPER_CALLS = {
    "refl-trans-closure": P("""(definductive refl-trans-closure
  :preds ((r* a b))
  :irules ((base ((r x y)) (r* x y))
           (refl () (r* x x))
           (trans ((r* x y) (r* y z)) (r* x z))))"""),
    "nat-trees": P("""(definductive nat-trees
  :preds ((nat n) (tree tr) (trees trs))
  :irules ((zero () (nat 0))
           (succ ((nat n)) (nat (1+ n)))
           (leaf ((nat n)) (tree n))
           (branch ((nat n) (trees trs)) (tree (cons n trs)))
           (empty () (trees nil))
           (cons ((tree tr) (trees trs)) (trees (cons tr trs)))))"""),
    "even-and-odd": P("""(definductive even-and-odd
  :preds ((even n) (odd n))
  :irules ((zero () (even 0))
           (from-even ((even n)) (odd (1+ n)))
           (from-odd ((odd n)) (even (1+ n)))))"""),
    "just-0": P("(definductive just-0 :preds ((p x)) :irules ((zero () (p 0))))"),
}
NO_PROOF_TREES = P("""(definductive no-proof-trees
  :preds ((p x))
  :irules ((recurse ((p x)) (p x))))""")

def call_parts(f):
    """(name, preds, irules, other-keyword-args) of a definductive form."""
    d = {}
    i = 2
    while i + 1 < len(f):
        d[f[i]] = f[i + 1]; i += 2
    other = {k: v for k, v in d.items() if k not in (":preds", ":irules")}
    return f[1] if len(f) > 1 else None, d.get(":preds"), d.get(":irules"), other

THM_HEADS = {"defthm", "defthmd", "defrule", "defruled", "defrulel", "defruledl", "thm", "defthm-nl"}

def theorems_with(forms, stmt):
    """defthm-like forms (anywhere, including under local / encapsulate / flag macros) with statement stmt."""
    out = []
    for f in forms:
        for l in subforms(f):
            if l and isinstance(l[0], str) and l[0] in THM_HEADS:
                s = l[1] if l[0] == "thm" else (l[2] if len(l) > 2 else None)
                if s == stmt:
                    out.append(l)
    return out

def instance_with(form, thm, bindings):
    """A (:instance thm ...) in form whose bindings include all of the given ones."""
    for l in subforms(form):
        if len(l) >= 2 and l[0] == ":instance" and l[1] == thm and all(b in l[2:] for b in bindings):
            return True
    return False

def main():
    d = sys.argv[1]
    for root, _, files in os.walk(d):
        for fn in files:
            if fn.endswith((".lisp", ".lsp", ".acl2")) and not fn.startswith(("grade-", "grader-")):
                src = open(os.path.join(root, fn), errors="replace").read()
                code = re.sub(r";[^\n]*", "", re.sub(r"#\|.*?\|#", " ", src, flags=re.S))
                for m in re.finditer(BANNED, code, re.I):
                    print(f"BANNED {os.path.relpath(os.path.join(root, fn), d)} {m.group(0)}")
    ex = os.path.join(d, "examples.lisp")
    if not os.path.exists(ex):
        for r in ("R2S", "R3S", "R4S"):
            print(f"{r} FAIL /work/examples.lisp is missing")
        return
    try:
        forms = strip_pkg(parse(tokens(open(ex, errors="replace").read())))
    except Exception as e:
        for r in ("R2S", "R3S", "R4S"):
            print(f"{r} FAIL examples.lisp does not parse ({e})")
        return
    top = [f[1] if isinstance(f, list) and len(f) == 2 and f[0] == "local" else f for f in forms]

    # ---------------- R2: the four calls, verbatim, at top level (not under must-fail/local)
    bad = []
    if not any(isinstance(f, list) and f[:2] == ["include-book", '"definductive"'] for f in top):
        bad.append('no (include-book "definductive")')
    tl = [f for f in forms if isinstance(f, list)]
    def toplevel_calls():
        out = []
        def walk(f):
            if not isinstance(f, list) or not f:
                return
            if f[0] == "definductive":
                out.append(f)
            elif f[0] in ("encapsulate", "progn", "defsection", "with-output"):
                for g in f[1:]:
                    walk(g)
        for f in tl:
            walk(f)
        return out
    calls = toplevel_calls()
    names = [c[1] for c in calls if len(c) > 1]
    stub = P("(defstub r (* *) => *)")
    stub_idx = next((i for i, f in enumerate(tl) if f == stub or any(g == stub for g in subforms(f))), None)
    rtc_idx = next((i for i, f in enumerate(tl) if any(isinstance(g, list) and g[:2] == ["definductive", "refl-trans-closure"] for g in subforms(f))), None)
    if stub_idx is None:
        bad.append("no (defstub r (* *) => *)")
    elif rtc_idx is not None and stub_idx > rtc_idx:
        bad.append("(defstub r (* *) => *) comes after refl-trans-closure")
    notes = []
    for nm, paper in PAPER_CALLS.items():
        mine = [c for c in calls if len(c) > 1 and c[1] == nm]
        if not mine:
            bad.append(f"no top-level call (definductive {nm} ...)")
            continue
        pn, pp, pi, _ = call_parts(paper)
        ok = False
        for c in mine:
            n, p, i, other = call_parts(c)
            if p == pp and i == pi:
                ok = True
                if other:
                    notes.append(f"{nm} has extra options {sorted(other)}")
        if not ok:
            bad.append(f"(definductive {nm} ...) differs from the paper's :preds/:irules")
    print("R2S " + ("PASS" if not bad else "FAIL " + "; ".join(bad)))
    if notes:
        print("R2NOTE " + "; ".join(notes))

    # ---------------- R3: hint parts shown in Section 5
    bad = []
    S = lambda s: P(s)
    tbl = theorems_with(forms, S("(implies (and (r x y) (r* y z)) (r* x z))"))
    if not any(any(contains(v, "r*-base") for v in kwarg(t, ":use")) for t in tbl):
        bad.append("trans-base-left: no theorem with a :use hint of r*-base (fn. 11)")
    rf = theorems_with(forms, S("(implies (r* a b) (r* (f a) (f b)))"))
    def ind_ok(t):
        return (S("(r* a b)") in kwarg(t, ":induct")
                and any(contains(v, S("(r* a b)")) and contains(v, S("(r*-proof-validp (r*-proof a b) a b)"))
                        for v in kwarg(t, ":expand"))
                and all(contains(t, x) for x in ("r*-base", "r*-refl", "r*-trans")))
    if not any(ind_ok(t) for t in rf):
        bad.append("r*-of-f: no proof with :induct (r* a b), :expand ((r* a b) (r*-proof-validp (r*-proof a b) a b)) "
                   "and enabling r*-base r*-refl r*-trans (Sec. 5.4)")
    lam = S("(r*-alt (lambda (a b) (r* (f a) (f b))))")
    def fi_ok(t):
        return (any(l[:2] == [":functional-instance", "r*-alt-when-r*"] and lam in l[2:] for l in subforms(t))
                and all(contains(t, x) for x in ("r*-base", "r*-refl", "r*-trans")))
    if not any(fi_ok(t) for t in rf):
        bad.append("r*-of-f: no proof by (:functional-instance r*-alt-when-r* (r*-alt (lambda (a b) (r* (f a) (f b))))) "
                   "enabling r*-base r*-refl r*-trans (Sec. 5.5)")
    for nm, stmt, inst in (("even-when-evenp", "(implies (and (natp n) (evenp n)) (even n))",
                            ("even-when-proof-validp", ["(proof (proof-for-even n))"])),
                           ("odd-when-oddp", "(implies (and (natp n) (oddp n)) (odd n))",
                            ("odd-when-proof-validp", ["(proof (proof-for-odd n))"])),
                           ("even-of-pred-when-odd", "(implies (odd n) (even (1- n)))",
                            ("even-when-proof-validp",
                             ["(proof (odd-proof-from-even->premise1-proof (odd-proof n)))", "(n (1- n))"]))):
        ts = theorems_with(forms, S(stmt))
        if not any(instance_with(t, inst[0], [S(b) for b in inst[1]]) for t in ts):
            bad.append(f"{nm}: no proof with (:instance {inst[0]} {' '.join(inst[1])}) (Sec. 5.2)")
    flag_ok = False
    for f in forms:
        for l in subforms(f):
            if l and l[0] == "defthm-even-proof-validp-clique-flag":
                e = theorems_with([l], S("(implies (even-proof-validp proof n) (natp n))"))
                o = theorems_with([l], S("(implies (odd-proof-validp proof n) (natp n))"))
                if (any("even-proof-validp" in kwarg(t, ":flag") for t in e)
                        and any("odd-proof-validp" in kwarg(t, ":flag") for t in o)):
                    flag_ok = True
    if not flag_ok:
        bad.append("natp-when-even/odd-proof-validp: not proved by defthm-even-proof-validp-clique-flag "
                   "with :flag even-proof-validp / odd-proof-validp (Sec. 5.3)")
    print("R3S " + ("PASS" if not bad else "FAIL " + "; ".join(bad)))

    # ---------------- R4: must-fail forms
    bad = []
    mfs = []
    for f in forms:
        for l in subforms(f):
            if l and l[0] == "must-fail" and len(l) > 1 and isinstance(l[1], list) and l[1][:1] == ["definductive"]:
                mfs.append(l[1])
    if not any(call_parts(c)[1:3] == call_parts(NO_PROOF_TREES)[1:3] and c[1] == "no-proof-trees" for c in mfs):
        bad.append("no (must-fail (definductive no-proof-trees ...)) with the paper's inputs")
    for conn in ("and", "or", "not", "implies"):
        found = False
        for c in mfs:
            _, preds, irules, _ = call_parts(c)
            if not isinstance(preds, list) or not isinstance(irules, list):
                continue
            pnames = {p[0] for p in preds if isinstance(p, list) and p and isinstance(p[0], str)}
            for r in irules:
                if isinstance(r, list) and len(r) == 3 and isinstance(r[1], list):
                    for prem in r[1]:
                        if (isinstance(prem, list) and prem[:1] == [conn]
                                and any(isinstance(g, list) and g and isinstance(g[0], str) and g[0] in pnames for g in subforms(prem[1:]))):
                            found = True
        if not found:
            bad.append(f"no must-fail definductive with a premise ({conn} ...) of a defined predicate")
    print("R4S " + ("PASS" if not bad else "FAIL " + "; ".join(bad)))

if __name__ == "__main__":
    main()
