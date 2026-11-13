#!/bin/sh
# V1+V2 on ACL2 8.7, V3 on ACL2 master (needs master's projects/fields certified).
set -e
G=/home/user/acl2-exp/exp2/given/russinoff-fields
S=${1:-<scratch>/given-russinoff-fields/rerun}
rm -rf "$S"; mkdir -p "$S/v1" "$S/v3" "$S/cmp"
cp $G/defs.lisp $G/cert.acl2 $G/verify/test-skip.lisp $G/verify/test-skip.acl2 "$S/v1/"
(cd "$S/v1" && perl /opt/acl2/books/build/cert.pl --acl2 /opt/acl2/saved_acl2 defs.lisp test-skip.lisp)
cp $G/cert.acl2 $G/verify/v3-authors.lisp "$S/v3/"
(cd "$S/v3" && perl /opt/acl2-master/books/build/cert.pl --acl2 /opt/acl2-master/saved_acl2 v3-authors.lisp)
cp $G/verify/dump.lsp $G/verify/run87.lsp $G/verify/runmaster.lsp "$S/cmp/"
cd "$S/cmp"
echo '(ld "run87.lsp")' | /opt/acl2/saved_acl2 > out87.txt 2>&1
echo '(ld "runmaster.lsp")' | /opt/acl2-master/saved_acl2 > outmaster.txt 2>&1
ex() { awk '/^@@ /{p=1} p' $1 | sed '/^ACL2 !>/,$d'; }
ex out87.txt > d87.txt; ex outmaster.txt > dmaster.txt
grep -c '^@@' d87.txt; diff d87.txt dmaster.txt && echo IDENTICAL
python3 -I $G/verify/match-targets.py $G/verify/v3-authors.lisp $G/targets.lisp
