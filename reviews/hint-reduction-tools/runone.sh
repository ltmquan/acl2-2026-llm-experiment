#!/bin/bash
# certify variant dir $1; print "<idx> PASS|FAIL <seconds>"
d=$1; i=$(basename $d); cd $d
s=$(date +%s)
if timeout 180 perl /root/acl2/books/build/cert.pl -q --acl2 /root/acl2/saved_acl2 solution.lisp >/dev/null 2>&1 && [ -f solution.cert ]; then r=PASS; else r=FAIL; fi
echo "$i $r $(( $(date +%s) - s ))"
