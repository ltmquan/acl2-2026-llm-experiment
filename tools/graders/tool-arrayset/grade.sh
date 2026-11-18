#!/bin/bash
# Grader for tool-arrayset (paper hardin-arrayset, ACL2 8.7).  Usage: grade.sh <work-dir>
# Prints one line per requirement (R1..R5: PASS / FAIL <reason> / MANUAL <what to inspect>) and a summary.
# Exit 0 iff every non-MANUAL requirement passes.  See CHECKLIST.md for the MANUAL items, NOTES.md for
# the interpretation and the validation.
set -u
WORK=$(cd "$1" && pwd)
G=$(cd "$(dirname "$0")" && pwd)
ACL2=/opt/acl2/saved_acl2
CERT=/opt/acl2/books/build/cert.pl
PY="python3 -I $G/check.py"
T=$(mktemp -d /tmp/grade-tool-arrayset-XXXXXX)
W=$T/work
cp -r "$WORK" "$W"
# drop any certificates and compiled files the model left, so that everything is certified here
find "$W" \( -name '*.cert' -o -name '*.cert.out' -o -name '*.port' -o -name '*.fasl' -o -name '*.lx64fsl' \
  -o -name '*.pcert0' -o -name '*.pcert1' -o -name '*.acl2x' -o -name '*.cert.time' \) -delete
echo "grading copy: $T"
declare -A RES
say() { RES[$1]="$2"; }

# ------------------------------------------------------------------ banned events
B=$($PY banned "$W")
if [ -n "$B" ]; then
  echo "BANNED events:"; echo "$B"
  for r in 1 2 3 4 5; do echo "R$r FAIL banned event in the model's files (see above)"; done
  echo "SUMMARY: FAIL (banned events)"; exit 1
fi

# ------------------------------------------------------------------ R1: Rust source
R1=$($PY r1 "$W" "$G"); r1rc=$?
RS="$W/src/arrayset.rs"
if [ -f "$RS" ]; then
  mkdir -p $T/rustc
  ok=""
  for args in "--edition 2021 --crate-type lib" "--crate-type lib" "--edition 2021" ""; do
    if rustc $args -o $T/rustc/out "$RS" > $T/rustc/log 2>&1; then ok="rustc $args"; break; fi
  done
  if [ -z "$ok" ]; then say 1 "FAIL src/arrayset.rs does not compile with rustc (see $T/rustc/log)"
  elif [ $r1rc = 0 ]; then say 1 "PASS (compiles with '$ok'; struct and the five functions match Sec. 5.1/Figs. 5-6 token for token)"
  elif [ $r1rc = 2 ]; then say 1 "MANUAL compiles with '$ok', but differs from the figures (CHECKLIST R1):
$(echo "${R1#MANUAL }" | sed 's/^/    /')"
  else say 1 "${R1}"; fi
else
  say 1 "FAIL /work/src/arrayset.rs missing"
fi

# ------------------------------------------------------------------ R5: certify every model book
$PY books "$W" > $T/books.txt
mapfile -t BOOKS < $T/books.txt
CERTFAIL=()
if [ ${#BOOKS[@]} -gt 0 ]; then
  (cd "$W" && timeout 4h perl $CERT --acl2 $ACL2 -j 4 -k "${BOOKS[@]}") > $T/cert-model.log 2>&1
  for b in "${BOOKS[@]}"; do [ -f "$W/${b%.lisp}.cert" ] || CERTFAIL+=("$b"); done
fi
if [ ${#BOOKS[@]} = 0 ]; then say 5 "FAIL no .lisp books in /work"
elif [ ${#CERTFAIL[@]} = 0 ]; then say 5 "PASS (${#BOOKS[@]} books: ${BOOKS[*]})"
else say 5 "FAIL not certified: ${CERTFAIL[*]} (see $T/cert-model.log; CHECKLIST R5 if one is not meant as a book)"; fi
certified() { [ -f "$W/${1%.lisp}.cert" ]; }

# ------------------------------------------------------------------ R2: RAC translation
mapfile -t GEN < <($PY gen "$W")
if [ ! -f "$W/README.md" ]; then
  say 2 "FAIL /work/README.md missing (it must give the commands)"
elif [ ${#GEN[@]} = 0 ]; then
  say 2 "FAIL no generated ACL2 file defines ASET_DEL"
else
  gen=${GEN[0]}; msgs=(); st=PASS
  [ ${#GEN[@]} -gt 1 ] && msgs+=("several files define ASET_DEL (${GEN[*]}); checked $gen")
  # (a) Figure 7 shape
  F7=$($PY fig7 "$W/$gen" "$G"); f7=$?
  if [ $f7 = 1 ]; then st=FAIL; fi
  [ $f7 = 2 ] && [ $st = PASS ] && st=MANUAL
  msgs+=("Fig. 7: $F7")
  # (b) all the functions were translated
  miss=""
  for fn in free_head used_head aset_add aset_del_head aset_del aset_transfer aset_find_val_from aset_init; do
    [ "$($PY formals "$W/$gen" $fn)" = NONE ] && miss="$miss $fn"
  done
  if [ -n "$miss" ]; then st=FAIL; msgs+=("not in $gen:$miss"); fi
  # (c) certifies against rtl/rel11/lib/rac
  if ! certified "$gen"; then st=FAIL; msgs+=("$gen does not certify");
  elif ! grep -qi 'rtl/rel11/lib/rac' "$W/$gen" "$W/${gen%.lisp}.acl2" "$(dirname "$W/$gen")/cert.acl2" 2>/dev/null; then
    st=FAIL; msgs+=("$gen does not include rtl/rel11/lib/rac"); fi
  # (d) re-run the RAC translator on the RAC source next to it (rac writes foo.lisp from foo.cpp)
  src="${gen%.lisp}.cpp"
  mkdir -p $T/rac-build
  cp -r /opt/acl2/books/projects/rac $T/rac-build/rac
  RACD=$T/rac-build/rac
  ( cd $RACD/src && make release RAC=$RACD ACL2=$ACL2 && make rac RAC=$RACD ACL2=$ACL2 \
    && mkdir -p ../bin && cp parse rac ../bin/ && chmod +x ../bin/rac ../bin/parse ) > $T/rac-build/build.log 2>&1
  if [ ! -x $RACD/bin/rac ]; then
    st=FAIL; msgs+=("grader could not build RAC (see $T/rac-build/build.log)")
  elif [ ! -f "$W/$src" ]; then
    [ $st = PASS ] && st=MANUAL
    msgs+=("no RAC source $src next to $gen: regenerate by hand following README.md (CHECKLIST R2)")
  else
    R=$T/regen; mkdir -p $R
    cp "$(dirname "$W/$src")"/*.cpp "$(dirname "$W/$src")"/*.h "$R"/ 2>/dev/null
    b=$(basename "${src%.cpp}")
    rm -f "$R/$b.lisp"
    (cd $R && bash $RACD/bin/rac -a "$b.cpp") > $R/rac.log 2>&1; racrc=$?
    if [ $racrc != 0 ] || [ ! -f "$R/$b.lisp" ]; then
      st=FAIL; msgs+=("RAC translator fails on $src (see $R/rac.log, $R/$b.acl2.log)")
    elif ! [ -f "$R/$b.cert" ]; then
      st=FAIL; msgs+=("regenerated $b.lisp does not certify against rtl/rel11/lib/rac (see $R/$b.acl2.log)")
    else
      SF=$($PY sameforms "$R/$b.lisp" "$W/$gen")
      if [ $? = 0 ]; then msgs+=("rac -a $src reproduces $gen and certifies against rtl/rel11/lib/rac")
      else [ $st = PASS ] && st=MANUAL; msgs+=("rac -a $src output $SF from $gen (CHECKLIST R2)"); fi
    fi
  fi
  [ $st = PASS ] && msgs+=("also inspect CHECKLIST R2(e): the RAC source corresponds to src/arrayset.rs")
  say 2 "$st $(printf '%s; ' "${msgs[@]}")"
fi

# ------------------------------------------------------------------ grader books
Z=$W/zz-grader
mkdir -p $Z
cp $G/grade-r4-*.lisp $G/grade-r4v.lisp $G/grade-r3x.lisp $Z/
echo "; grader books: no portcullis" > $Z/cert.acl2
gen_model_book() {  # $@ = model books to include
  { echo '(in-package "ACL2")'; echo '; generated by grade.sh: includes the model books'
    for b in "$@"; do echo "(include-book \"../${b%.lisp}\")"; done; } > $Z/grader-model.lisp
  rm -f $Z/grader-model.cert
  (cd $Z && perl $CERT --acl2 $ACL2 grader-model.lisp) > $T/cert-grader-model.log 2>&1
  [ -f $Z/grader-model.cert ]
}
OKB=(); for b in "${BOOKS[@]}"; do certified "$b" && OKB+=("$b"); done
MODEL_OK=no; MODEL_NOTE=
if gen_model_book "${OKB[@]}"; then MODEL_OK=yes
else
  mapfile -t DEF < <($PY defines "$W" aset_add-val-at-used_head--thm aset_del-val-at-free_head--thm \
    aset_del_head-used-list--thm aset_del_head-free-list--thm asetp)
  OKD=(); for b in "${DEF[@]}"; do certified "$b" && OKD+=("$b"); done
  if [ ${#OKD[@]} -gt 0 ] && gen_model_book "${OKD[@]}"; then MODEL_OK=yes
  else
    # The defining books may themselves conflict, e.g. two instances of the arrayset with different
    # ARR_SZ that define the same names. Use the first defining book that loads on its own.
    mapfile -t DEFT < <($PY defines "$W" aset_add-val-at-used_head--thm aset_del-val-at-free_head--thm \
      aset_del_head-used-list--thm aset_del_head-free-list--thm)
    for b in "${DEFT[@]}"; do
      certified "$b" || continue
      if gen_model_book "$b"; then MODEL_OK=yes; MODEL_NOTE="graded on $b alone (the model's books define the same names in several instances)"; break; fi
    done
  fi
fi
# grader-init: how to build an initial arrayset with the model's aset_init (the paper does not fix its arity)
INIT=NONE
[ ${#GEN[@]} -gt 0 ] && INIT=$($PY formals "$W/${GEN[0]}" aset_init)
{ echo '(in-package "RTL")'; echo '(include-book "grader-model")'
  case $INIT in
    0) echo "(defmacro grader-init () '(aset_init))";;
    1) echo "(defmacro grader-init () '(aset_init nil))";;
  esac; } > $Z/grader-init.lisp
cert_grader() { (cd $Z && timeout 2h perl $CERT --acl2 $ACL2 "$1.lisp") > $T/cert-$1.log 2>&1; [ -f $Z/$1.cert ]; }

# ------------------------------------------------------------------ R4: the four theorems, verbatim, :by
if [ $MODEL_OK = no ]; then
  say 4 "FAIL the model's books cannot be included together (see $T/cert-grader-model.log)"
else
  bad=()
  for i in 1 2 3 4; do cert_grader grade-r4-$i || bad+=("$(sed -n 's/^;; *THEOREM: *//p' $G/grade-r4-$i.lisp)"); done
  if [ ${#bad[@]} -gt 0 ]; then
    say 4 "FAIL not proved verbatim (:by) from the model's theorem of the same name: ${bad[*]} (see $T/cert-grade-r4-*.log)"
  elif [ "$INIT" != 0 ] && [ "$INIT" != 1 ]; then
    say 4 "MANUAL the four theorems hold verbatim; non-vacuity not run (aset_init has ${INIT} formals): CHECKLIST R4"
  elif cert_grader grade-r4v; then
    say 4 "PASS (four theorems verbatim by :by; hypotheses satisfiable on the Fig. 4(a) instance built with aset_init/aset_add${MODEL_NOTE:+; $MODEL_NOTE})"
  else
    say 4 "FAIL theorems hold, but the non-vacuity check failed: hypotheses false on the Fig. 4(a) instance (see $T/cert-grade-r4v.log)"
  fi
fi

# ------------------------------------------------------------------ R3: examples.lisp
EX=$($PY examples "$W")
if [[ $EX == FAIL* ]]; then say 3 "$EX"
elif ! certified examples.lisp; then say 3 "FAIL /work/examples.lisp does not certify"
else
  X="grader's own Fig. 4(b) execution check (grade-r3x) not run"
  if [ $MODEL_OK = yes ] && { [ "$INIT" = 0 ] || [ "$INIT" = 1 ]; }; then
    if cert_grader grade-r3x; then X="grader's own Fig. 4(b) execution check PASSES"
    else X="grader's own Fig. 4(b) execution check FAILS (see $T/cert-grade-r3x.log)"; fi
  fi
  say 3 "MANUAL examples.lisp certifies, ${EX#OK }; inspect it per CHECKLIST R3 ($X)"
fi

# ------------------------------------------------------------------ report
fail=0; man=0
for r in 1 2 3 4 5; do
  echo "R$r ${RES[$r]}"
  case "${RES[$r]}" in FAIL*) fail=$((fail+1));; MANUAL*) man=$((man+1));; esac
done
if [ $fail = 0 ]; then echo "SUMMARY: PASS ($man MANUAL item(s) to inspect, see CHECKLIST.md)"; exit 0
else echo "SUMMARY: FAIL ($fail requirement(s) failed, $man MANUAL)"; exit 1; fi
