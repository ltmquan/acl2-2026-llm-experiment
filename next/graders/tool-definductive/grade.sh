#!/bin/bash
# Grader for tool-definductive (ACL2 8.7).
# Usage: grade.sh <work-dir>     (a copy of the model's /work)
# Prints one line per requirement (R1..R6: PASS / FAIL <reason> / MANUAL) and a summary line.
# Exit 0 iff every non-MANUAL requirement passes.
# ACL2 and CERT may be overridden from the environment (used only for validation).
set -u
G=$(cd "$(dirname "$0")" && pwd)
W=${1:?usage: grade.sh <work-dir>}
ACL2=${ACL2:-/opt/acl2/saved_acl2}
CERT=${CERT:-/opt/acl2/books/build/cert.pl}
TMO=${TMO:-3600}
T=$(mktemp -d "${TMPDIR:-/tmp}/grade-tool-definductive.XXXXXX")
echo "work copy: $T"
cp -r "$W"/. "$T"/
find "$T" \( -name '*.cert' -o -name '*.cert.out' -o -name '*.fasl' -o -name '*.port' -o -name '*.pcert*' \
          -o -name '*.lx64fsl' -o -name '*.dx64fsl' -o -name '*.acl2x' -o -name 'Makefile-tmp' \) -delete
# default cert flags only: drop cert-flags comments from .acl2 files
find "$T" -name '*.acl2' -exec sed -i '/cert-flags/d' {} +

declare -A RES
setfail() { RES[$1]="FAIL $2"; }

# --- 0. setup: our books must not collide with the model's files
for f in "$G"/grade-*.lisp "$G"/grader-*.lisp "$G"/r4-bad-calls.lsp; do
  b=$(basename "$f")
  if [ -e "$T/$b" ]; then echo "SETUP: the work dir has a file named $b; it is replaced by the grader's"; fi
  cp "$f" "$T/$b"
done

# --- 1. static checks (banned events; examples.lisp contents)
python3 -I "$G/check-examples.py" "$T" > "$T/static.txt" 2>&1 || echo "R2S FAIL static checker crashed" >> "$T/static.txt"
cat "$T/static.txt" | sed 's/^/static: /'
BANNED=$(grep '^BANNED' "$T/static.txt" | tr '\n' ' ')
st() { grep "^$1 " "$T/static.txt" | head -1 | cut -d' ' -f2-; }

# --- 2. certification helpers
certify() { # certify <book-basename-without-.lisp>; returns 0 on success
  (cd "$T" && timeout "$TMO" "$CERT" --acl2 "$ACL2" "$1.lisp" > "$T/$1.certpl.log" 2>&1)
  [ -f "$T/$1.cert" ]
}
reason() { # reason <book>: the GRADER-FAIL labels, or the first ACL2 error
  local out="$T/$1.cert.out" fails
  if [ ! -f "$out" ]; then
    echo "certification of $1 did not run or a book it includes failed: $(grep -h -m1 -E 'FAILED|missing|Error' "$T/$1.certpl.log" | head -c 300)"
    return
  fi
  fails=$(grep -h '^GRADER-FAIL ' "$out" | sed 's/^GRADER-FAIL //; s/:.*//' | sort -u | tr '\n' ' ')
  if [ -n "$fails" ]; then echo "failed checks: $fails(see $out)"; return; fi
  echo "$1 does not certify: $(grep -h -m1 -A2 'ACL2 Error' "$out" | tr '\n' ' ' | tr -s ' ' | head -c 400)"
}

if [ -n "$BANNED" ]; then
  for r in R1 R2 R3 R4 R5 R6; do setfail $r "banned event(s): $BANNED"; done
else
  # --- R6: the model's books certify
  certify definductive; DOK=$?
  certify examples; EOK=$?
  if [ $DOK -eq 0 ] && [ $EOK -eq 0 ]; then RES[R6]=PASS
  else setfail R6 "$( [ $DOK -ne 0 ] && echo "definductive.lisp: $(reason definductive)") $( [ $EOK -ne 0 ] && echo "examples.lisp: $(reason examples)")"; fi

  # --- R1: generated events of the paper's examples (needs grade-r2)
  if certify grade-r1; then RES[R1]=PASS; else setfail R1 "$(reason grade-r1) $( [ -f "$T/grade-r2.cert" ] || echo '[the paper calls (grade-r2) failed]')"; fi

  # --- R2: examples.lisp has the paper's calls; the tool admits them; the predicates exist after examples.lisp
  r2=""
  [ "$(st R2S)" = PASS ] || r2="$r2 examples.lisp: $(st R2S);"
  certify grade-r2 || r2="$r2 the paper's calls are not admitted: $(reason grade-r2);"
  if [ $EOK -eq 0 ]; then certify grade-r2x || r2="$r2 $(reason grade-r2x);"; else r2="$r2 examples.lisp does not certify;"; fi
  if [ -z "$r2" ]; then RES[R2]=PASS; else setfail R2 "$r2"; fi

  # --- R3: Section 5 theorems in examples.lisp (statements, hints) and with the paper's hints on the tool
  r3=""
  [ "$(st R3S)" = PASS ] || r3="$r3 examples.lisp hints: $(st R3S);"
  if [ $EOK -eq 0 ]; then certify grade-r3 || r3="$r3 examples.lisp statements: $(reason grade-r3);"; else r3="$r3 examples.lisp does not certify;"; fi
  certify grade-r3-paper || r3="$r3 paper proofs on the tool: $(reason grade-r3-paper);"
  if [ -z "$r3" ]; then RES[R3]=PASS; else setfail R3 "$r3"; fi

  # --- R4: rejections (must-fail in examples.lisp; our must-fail book; ACL2 error, not raw Lisp error)
  r4=""
  [ "$(st R4S)" = PASS ] || r4="$r4 examples.lisp: $(st R4S);"
  certify grade-r4 || r4="$r4 $(reason grade-r4);"
  if [ $DOK -eq 0 ]; then
    i=0
    python3 -I -c '
import re, sys
blocks = re.split(r"(?m)^;;;;$", open(sys.argv[1]).read())
k = 0
for b in blocks:
    lines = [l for l in b.splitlines() if l.strip() and not l.lstrip().startswith(";")]
    if not lines:
        continue
    open(sys.argv[2] + "/r4-run-%d.lsp" % k, "w").write(
        "(include-book \"definductive\")\n(cw \"@@@BEGIN@@@~%\")\n" + "\n".join(lines) +
        "\n(cw \"@@@END@@@~%\")\n")
    k += 1
' "$T/r4-bad-calls.lsp" "$T"
    for s in "$T"/r4-run-*.lsp; do
      o="${s%.lsp}.out"
      (cd "$T" && timeout "$TMO" "$ACL2" < "$s" > "$o" 2>&1)
      body=$(sed -n '/@@@BEGIN@@@/,$p' "$o")
      nm=$(grep -m1 -o '(definductive [^ ]*' "$s" | cut -d' ' -f2)
      if ! grep -q '@@@END@@@' <<< "$body" || grep -q 'ABORTING from raw Lisp' <<< "$body"; then
        r4="$r4 $nm: raw Lisp error or abort (see $o);"
      elif ! grep -q -E 'ACL2 Error|HARD ACL2 ERROR' <<< "$body"; then
        r4="$r4 $nm: no ACL2 error at the top level (see $o);"
      fi
    done
  else
    r4="$r4 definductive.lisp does not certify;"
  fi
  if [ -z "$r4" ]; then RES[R4]=PASS; else setfail R4 "$r4"; fi

  # --- R5: theory independence
  r5=""
  certify grade-r5-hostile || r5="$r5 with hostile rules: $(reason grade-r5-hostile);"
  if [ -z "$r5" ]; then RES[R5]=PASS; else setfail R5 "$r5"; fi
fi

ok=0; fails=0
for r in R1 R2 R3 R4 R5 R6; do
  echo "$r ${RES[$r]}"
  case "${RES[$r]}" in PASS) ok=$((ok+1));; *) fails=$((fails+1));; esac
done
echo "SUMMARY tool-definductive: $ok PASS, $fails FAIL, 0 MANUAL (see CHECKLIST.md for the human review of R1/R3 fills); logs in $T"
[ $fails -eq 0 ]
