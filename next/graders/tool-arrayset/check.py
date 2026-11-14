#!/usr/bin/env python3
"""Helper for grade.sh (tool-arrayset). Subcommands:

  banned  <work>                 banned events in the model's .lisp/.lsp/.acl2 files; prints the hits
  books   <work>                 the model's .lisp files to certify (relative paths), one per line
  r1      <work> <grader-dir>    R1: compare /work/src/arrayset.rs with fig5-6.rs (token level)
  gen     <work>                 the generated ACL2 files that define ASET_DEL (relative paths)
  fig7    <file> <grader-dir>    compare the ASET_DEL defund of <file> with fig7.lsp
  sameforms <a> <b>              do two ACL2 files have the same forms (ignoring comments/whitespace/case)?
  defines <work> <name>...       relative paths of model books that define (defthm/defun...) any <name>
  formals <file> <fn>            formals of the defun/defund <fn> in <file>, or NONE
  examples <work>                mechanical part of R3 on /work/examples.lisp

The banned-event list and the s-expression tokenizer/parser are copied from check-prove.py.
"""
import difflib, filecmp, os, re, sys

BANNED = (r"skip-proofs|defaxiom|defttag|set-ld-redefinition-action|skip-proofs-okp|:ttags|set-skip-proofs|"
          r"trust-tag|define-trusted-clause-processor|defun-unsound|sys-call|reset-prehistory|\bredef\b|set-cbd|"
          r"progn!|defattach-system|set-raw-mode|\bdefstobj\b.*:congruent-to")
RAC = "/opt/acl2/books/projects/rac"
GRADER_SUBDIR = "zz-grader"


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


def read_forms(path):
    return parse(tokens(open(path, errors="replace").read()))


def strip_pkg(x):
    if isinstance(x, str):
        return re.sub(r"^(rtl|acl2)::", "", x)
    return [strip_pkg(y) for y in x]


def exported(forms):
    out = []
    def walk(f):
        if not isinstance(f, list) or not f or f[0] == "local":
            return
        if f[0] == "encapsulate":
            for g in f[2:]: walk(g)
        elif f[0] in ("progn", "defsection", "defines", "skip-proofs"):
            for g in f[1:]: walk(g)
        elif f[0] == "define" and "///" in f:
            out.append(f)
            for g in f[f.index("///") + 1:]: walk(g)
        else:
            out.append(f)
    for f in forms: walk(f)
    return out


def pp(x, ind=0):
    """Pretty-print an s-expression, one subform per line, for diffs."""
    if not isinstance(x, list):
        return [" " * ind + x]
    if len(str(x)) < 70:
        return [" " * ind + flat(x)]
    lines = [" " * ind + "(" + flat(x[0]) if x else " " * ind + "("]
    for y in x[1:]:
        lines += pp(y, ind + 2)
    lines[-1] += ")"
    return lines


def flat(x):
    return x if not isinstance(x, list) else "(" + " ".join(flat(y) for y in x) + ")"


def rac_copy(path):
    """True if path is an unchanged copy of a file of books/projects/rac (the model may copy RAC to /work)."""
    b = os.path.basename(path)
    for root, _, files in os.walk(RAC):
        if b in files and filecmp.cmp(path, os.path.join(root, b), shallow=False):
            return True
    return False


def model_files(work, exts):
    out = []
    for root, dirs, files in os.walk(work):
        dirs[:] = [d for d in dirs if d != GRADER_SUBDIR and not d.startswith(".")]
        for f in files:
            if os.path.splitext(f)[1].lower() in exts:
                p = os.path.join(root, f)
                if not rac_copy(p):
                    out.append(p)
    return sorted(out)


def cmd_banned(work):
    hits = []
    for p in model_files(work, (".lisp", ".lsp", ".acl2")):
        src = open(p, errors="replace").read()
        code = re.sub(r";[^\n]*", "", re.sub(r"#\|.*?\|#", " ", src, flags=re.S))
        m = re.search(BANNED, code, re.I)
        if m:
            hits.append(f"{os.path.relpath(p, work)}: {m.group(0)}")
    print("\n".join(hits))
    return 1 if hits else 0


def cmd_books(work):
    for p in model_files(work, (".lisp",)):
        print(os.path.relpath(p, work))
    return 0


# ---------------------------------------------------------------- Rust (R1)

def rs_tokens(s):
    s = re.sub(r"/\*.*?\*/", " ", s, flags=re.S)
    s = re.sub(r"//[^\n]*", " ", s)
    toks = re.findall(r"[A-Za-z_][A-Za-z0-9_]*|\d+|&&|\|\||==|!=|<=|>=|->|=>|\+=|-=|::|\S", s)
    return [t for t in toks if t != "pub"]


def rs_block(toks, head):
    """Tokens from the first occurrence of the token sequence head through its matching closing brace."""
    n = len(head)
    for i in range(len(toks) - n + 1):
        if toks[i:i + n] == head:
            j = i + n
            while j < len(toks) and toks[j] != "{":
                j += 1
            depth = 0
            for k in range(j, len(toks)):
                depth += toks[k] == "{"
                depth -= toks[k] == "}"
                if depth == 0:
                    return toks[i:k + 1]
            return None
    return None


def cmd_r1(work, gdir):
    path = os.path.join(work, "src", "arrayset.rs")
    if not os.path.exists(path):
        print("FAIL /work/src/arrayset.rs missing"); return 1
    model = rs_tokens(open(path, errors="replace").read())
    paper = rs_tokens(open(os.path.join(gdir, "fig5-6.rs")).read())
    fails, diffs = [], []
    src = open(path, errors="replace").read()
    if not re.search(r"\bconst\s+ARR_SZ\s*:\s*\w+\s*=\s*1024\s*;", src):
        diffs.append("ARR_SZ is not declared as `const ARR_SZ: <type> = 1024;`")
    if not re.search(r"#\s*\[\s*derive\s*\(\s*Copy\s*,\s*Clone\s*\)\s*\]\s*(pub\s+)?struct\s+Arrayset\b", src):
        diffs.append("struct Arrayset is not preceded by #[derive(Copy, Clone)]")
    for name, head in [("struct Arrayset", ["struct", "Arrayset"]), ("free_head", ["fn", "free_head"]),
                       ("used_head", ["fn", "used_head"]), ("aset_add", ["fn", "aset_add"]),
                       ("aset_del_head", ["fn", "aset_del_head"]), ("aset_del", ["fn", "aset_del", "("])]:
        p, m = rs_block(paper, head), rs_block(model, head)
        if m is None:
            fails.append(f"{name} missing")
        elif p != m:
            d = "\n".join(difflib.unified_diff(p, m, "paper", "model", lineterm="", n=2))
            diffs.append(f"{name} differs from the paper (token diff):\n{d}")
    for name in ("aset_transfer", "aset_find_val_from", "aset_init"):
        if rs_block(model, ["fn", name]) is None:
            fails.append(f"{name} missing")
    if fails:
        print("FAIL " + "; ".join(fails)); return 1
    if diffs:
        print("MANUAL " + "\n".join(diffs)); return 2
    print("PASS"); return 0


# ---------------------------------------------------------------- generated ACL2 (R2)

def defun_of(forms, name):
    for f in exported(forms):
        f = strip_pkg(f)
        if isinstance(f, list) and len(f) >= 4 and f[0] in ("defund", "defun") and f[1] == name:
            return f
    return None


def cmd_gen(work):
    for p in model_files(work, (".lisp",)):
        try:
            if defun_of(read_forms(p), "aset_del") is not None:
                print(os.path.relpath(p, work))
        except Exception:
            pass
    return 0


def drop_bits(x):
    """(BITS x 63 0) -> x, recursively."""
    if not isinstance(x, list):
        return x
    if len(x) == 4 and x[0] == "bits" and x[2] == "63" and x[3] == "0":
        return drop_bits(x[1])
    return [drop_bits(y) for y in x]


def ops(x, acc):
    if isinstance(x, list):
        if x and isinstance(x[0], str): acc.add(x[0])
        for y in x: ops(y, acc)
    return acc


def cmd_fig7(path, gdir):
    m = defun_of(read_forms(path), "aset_del")
    p = strip_pkg(read_forms(os.path.join(gdir, "fig7.lsp"))[0])
    if m is None:
        print("FAIL no (DEFUND ASET_DEL ...) in " + path); return 1
    m = [m[0], m[1], m[2], m[-1]]  # ignore declarations
    if m == p:
        print("PASS identical to Figure 7"); return 0
    if drop_bits(m) == drop_bits(p):
        print("PASS identical to Figure 7 up to (BITS x 63 0) wrappers"); return 0
    need = {"ag", "as", "if1", "log<", "logand1", "log<>", "mv-let", "mv", "aset_find_val_from", "aset_del_head"}
    missing = need - ops(m, set())
    d = "\n".join(difflib.unified_diff(pp(p), pp(m), "Figure 7", "model", lineterm=""))
    if missing:
        print("FAIL generated ASET_DEL lacks " + " ".join(sorted(missing)) + "\n" + d); return 1
    print("MANUAL generated ASET_DEL differs from Figure 7:\n" + d); return 2


def cmd_sameforms(a, b):
    fa, fb = strip_pkg(read_forms(a)), strip_pkg(read_forms(b))
    if fa == fb:
        print("same"); return 0
    na = {f[1] if isinstance(f, list) and len(f) > 1 else flat(f): f for f in fa}
    nb = {f[1] if isinstance(f, list) and len(f) > 1 else flat(f): f for f in fb}
    diff = sorted(set(k for k in set(na) | set(nb) if na.get(k) != nb.get(k)))
    print("differ in: " + " ".join(diff)); return 1


def cmd_defines(work, names):
    names = set(n.lower() for n in names)
    for p in model_files(work, (".lisp",)):
        try:
            fs = exported(read_forms(p))
        except Exception:
            continue
        if any(isinstance(f, list) and len(f) > 1 and isinstance(f[1], str) and strip_pkg(f[1]) in names
               for f in fs):
            print(os.path.relpath(p, work))
    return 0


def cmd_formals(path, fn):
    f = defun_of(read_forms(path), fn.lower())
    print("NONE" if f is None else len(f[2]))
    return 0


def cmd_examples(work):
    p = os.path.join(work, "examples.lisp")
    if not os.path.exists(p):
        print("FAIL /work/examples.lisp missing"); return 1
    toks = tokens(open(p, errors="replace").read())
    forms = read_forms(p)
    def count(x, name):
        if isinstance(x, list):
            return (1 if x and x[0] == name else 0) + sum(count(y, name) for y in x)
        return 0
    n = sum(count(f, "assert-event") for f in forms)
    if n == 0:
        print("FAIL /work/examples.lisp has no assert-event"); return 1
    if not any(re.fullmatch(r"(rtl::)?aset_del", t) for t in toks):
        print("FAIL /work/examples.lisp never calls aset_del"); return 1
    lack = [v for v in ("22", "33") if v not in toks]
    print(f"OK {n} assert-event forms" + (f"; values {' and '.join(lack)} never appear" if lack else ""))
    return 0


def main():
    c, a = sys.argv[1], sys.argv[2:]
    f = {"banned": cmd_banned, "books": cmd_books, "r1": cmd_r1, "gen": cmd_gen, "fig7": cmd_fig7,
         "sameforms": cmd_sameforms, "formals": cmd_formals, "examples": cmd_examples}
    if c == "defines":
        sys.exit(cmd_defines(a[0], a[1:]))
    sys.exit(f[c](*a))


if __name__ == "__main__":
    main()
