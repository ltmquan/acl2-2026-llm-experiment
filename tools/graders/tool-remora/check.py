#!/usr/bin/env python3
"""Helper for grade.sh (tool-remora). Subcommands:

  banned  <work>                     banned events in the model's .lisp/.lsp/.acl2 files; prints the hits
  books   <work>                     the model's .lisp files to certify (relative paths), one per line
  defines <work> <name>...           model books that define any <name> (not under local)
  thm     <work> <targets> <name>    compare the model's defthm <name> with the paper's (targets.lisp):
                                     prints MISSING, SAME, or DIFF + a diff; then README:yes/no (is the
                                     name mentioned in /work/README.md)
  examples <work>                    mechanical part of R4 on /work/examples.lisp
  comm    <work>                     candidate commutativity theorems for R3 (names, one per line)

The banned-event list and the s-expression tokenizer/parser are copied from check-prove.py.
"""
import difflib, os, re, sys

BANNED = (r"skip-proofs|defaxiom|defttag|set-ld-redefinition-action|skip-proofs-okp|:ttags|set-skip-proofs|"
          r"trust-tag|define-trusted-clause-processor|defun-unsound|sys-call|reset-prehistory|\bredef\b|set-cbd|"
          r"progn!|defattach-system|set-raw-mode|\bdefstobj\b.*:congruent-to")
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
        return re.sub(r"^(remora|acl2)::", "", x)
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


def model_files(work, exts):
    out = []
    for root, dirs, files in os.walk(work):
        dirs[:] = [d for d in dirs if d != GRADER_SUBDIR and not d.startswith(".")]
        for f in files:
            if os.path.splitext(f)[1].lower() in exts:
                out.append(os.path.join(root, f))
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


THM_KINDS = ("defthm", "defthmd", "defrule", "defruled")


def cmd_thm(work, targets, name):
    name = name.lower()
    paper = {f[1]: f[2] for f in strip_pkg(read_forms(targets))}[name]
    found = None
    for p in model_files(work, (".lisp",)):
        try:
            fs = exported(read_forms(p))
        except Exception:
            continue
        for f in fs:
            f = strip_pkg(f)
            if isinstance(f, list) and len(f) >= 3 and f[0] in THM_KINDS and f[1] == name:
                found = (os.path.relpath(p, work), f[2]); break
        if found: break
    readme = os.path.join(work, "README.md")
    mentioned = os.path.exists(readme) and name in open(readme, errors="replace").read().lower()
    if found is None:
        print("MISSING")
    elif found[1] == paper:
        print(f"SAME (in {found[0]})")
    else:
        print(f"DIFF (in {found[0]}):")
        print("\n".join(difflib.unified_diff(pp(paper), pp(found[1]), "paper", "model", lineterm="")))
    print("README:" + ("yes" if mentioned else "no"))
    return 0


def cmd_comm(work):
    """Candidate commutativity theorems: a theorem mentioning (eval-app f (list a b) l) and
    (eval-app f (list b a) l) (list may also be written with cons)."""
    def lst(x):
        if isinstance(x, list) and x and x[0] == "list" and len(x) == 3:
            return (x[1], x[2])
        if isinstance(x, list) and len(x) == 3 and x[0] == "cons" and isinstance(x[2], list) \
           and len(x[2]) == 3 and x[2][0] == "cons" and x[2][2] in ("nil", "'nil", ["quote", "nil"]):
            return (x[1], x[2][1])
        return None
    def apps(x, acc):
        if isinstance(x, list):
            if len(x) == 4 and x[0] == "eval-app" and lst(x[2]):
                acc.append((flat(x[1]), lst(x[2]), flat(x[3])))
            for y in x: apps(y, acc)
        return acc
    for p in model_files(work, (".lisp",)):
        try:
            fs = exported(read_forms(p))
        except Exception:
            continue
        for f in fs:
            f = strip_pkg(f)
            if isinstance(f, list) and len(f) >= 3 and f[0] in THM_KINDS:
                a = apps(f[2], [])
                if any(x[0] == y[0] and x[2] == y[2] and x[1][0] == y[1][1] and x[1][1] == y[1][0]
                       and x[1][0] != x[1][1] for x in a for y in a):
                    print(f"{f[1]} ({os.path.relpath(p, work)})")
    return 0


def cmd_examples(work):
    p = os.path.join(work, "examples.lisp")
    if not os.path.exists(p):
        print("FAIL /work/examples.lisp missing"); return 1
    forms = read_forms(p)
    def count(x, name):
        if isinstance(x, list):
            return (1 if x and x[0] == name else 0) + sum(count(y, name) for y in x)
        return 0
    n = sum(count(f, "assert-event") for f in forms)
    if n == 0:
        print("FAIL /work/examples.lisp has no assert-event"); return 1
    print(f"OK {n} assert-event forms")
    return 0


def main():
    c, a = sys.argv[1], sys.argv[2:]
    if c == "defines":
        sys.exit(cmd_defines(a[0], a[1:]))
    f = {"banned": cmd_banned, "books": cmd_books, "thm": cmd_thm, "examples": cmd_examples, "comm": cmd_comm}
    sys.exit(f[c](*a))


if __name__ == "__main__":
    main()
