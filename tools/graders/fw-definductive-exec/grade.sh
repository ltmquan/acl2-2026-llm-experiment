#!/bin/bash
# Grader for fw-definductive-exec (ACL2 master 1d2b39a424).
# Usage: grade.sh <work-dir>     (a copy of the model's /work)
# Prints R1..R4 (PASS / FAIL <reason>), the extra check H2 (informative, not counted in the exit code),
# and a summary line. Exit 0 iff R1..R4 pass.
# ACL2 and CERT may be overridden from the environment (validation only).
set -u
G=$(cd "$(dirname "$0")" && pwd)
W=${1:?usage: grade.sh <work-dir>}
ACL2=${ACL2:-/opt/acl2-master/saved_acl2}
CERT=${CERT:-/opt/acl2-master/books/build/cert.pl}
BOOKS=${BOOKS:-/opt/acl2-master/books}
TMO=${TMO:-3600}
T=$(mktemp -d "${TMPDIR:-/tmp}/grade-fw-definductive-exec.XXXXXX")
echo "work copy: $T"
cp -r "$W"/. "$T"/
find "$T" \( -name '*.cert' -o -name '*.cert.out' -o -name '*.fasl' -o -name '*.port' -o -name '*.pcert*' \
          -o -name '*.lx64fsl' -o -name '*.dx64fsl' -o -name '*.acl2x' -o -name 'Makefile-tmp' \) -delete
# default cert flags only: drop cert-flags comments (e.g. "; cert-flags: ? t :ttags :all" copied from std/util/cert.acl2)
find "$T" -name '*.acl2' -exec sed -i '/cert-flags/d' {} +

declare -A RES
setfail() { RES[$1]="FAIL $2"; }

for f in "$G"/grade-*.lisp "$G"/grader-*.lisp; do
  b=$(basename "$f")
  [ -e "$T/$b" ] && echo "SETUP: the work dir has a file named $b; it is replaced by the grader's"
  cp "$f" "$T/$b"
done
# R2: the books' definductive-tests.lisp, unchanged; its (include-book "definductive") now finds the
# model's definductive.lisp, because the copy sits next to it.
cp "$BOOKS/std/util/definductive-tests.lisp" "$T/grade-r2-definductive-tests.lisp"
cmp -s "$BOOKS/std/util/definductive-tests.lisp" "$T/grade-r2-definductive-tests.lisp" || echo "SETUP: tests copy differs"
grep -q '^(include-book "definductive")' "$T/grade-r2-definductive-tests.lisp" || echo "SETUP: tests do not include \"definductive\""

python3 -I "$G/check-exec.py" "$T" "$BOOKS/std/util/definductive.lisp" > "$T/static.txt" 2>&1 \
  || echo "R3S FAIL static checker crashed" >> "$T/static.txt"
sed 's/^/static: /' "$T/static.txt"
BANNED=$(grep '^BANNED' "$T/static.txt" | tr '\n' ' ')
st() { grep "^$1 " "$T/static.txt" | head -1 | cut -d' ' -f2-; }

certify() {
  (cd "$T" && timeout "$TMO" "$CERT" --acl2 "$ACL2" "$1.lisp" > "$T/$1.certpl.log" 2>&1)
  [ -f "$T/$1.cert" ]
}
reason() {
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
  for r in R1 R2 R3 R4 H2; do setfail $r "banned event(s): $BANNED"; done
else
  r1=""
  [ "$(st R1S)" = PASS ] || r1="$r1 $(st R1S);"
  certify grade-r1 || r1="$r1 $(reason grade-r1);"
  if [ -z "$r1" ]; then RES[R1]=PASS; else setfail R1 "$r1"; fi

  if certify grade-r2-definductive-tests; then RES[R2]=PASS
  else setfail R2 "the books' definductive-tests.lisp does not certify on the model's definductive.lisp: $(reason grade-r2-definductive-tests)"; fi

  r3=""
  [ "$(st R3S)" = PASS ] || r3="$r3 $(st R3S);"
  if certify exec-tests; then EOK=0; else EOK=1; r3="$r3 exec-tests.lisp: $(reason exec-tests);"; fi
  if [ -z "$r3" ]; then RES[R3]=PASS; else setfail R3 "$r3"; fi

  if certify grade-hidden; then RES[R4]=PASS; else setfail R4 "hidden :exec definitions (grade-hidden.lisp): $(reason grade-hidden)"; fi
  if [ $EOK -eq 0 ]; then
    if certify grade-h2; then RES[H2]=PASS; else setfail H2 "$(reason grade-h2)"; fi
  else setfail H2 "exec-tests.lisp does not certify"; fi
fi

ok=0; fails=0
for r in R1 R2 R3 R4; do
  echo "$r ${RES[$r]}"
  case "${RES[$r]}" in PASS) ok=$((ok+1));; *) fails=$((fails+1));; esac
done
echo "H2 ${RES[H2]}   (informative: e-correct / booleanp-of-e forms and executability for exec-tests.lisp's own definitions; not counted)"
echo "SUMMARY fw-definductive-exec: $ok PASS, $fails FAIL, 0 MANUAL (R1-R4); informative H2 ${RES[H2]%% *}; logs in $T"
[ $fails -eq 0 ]
