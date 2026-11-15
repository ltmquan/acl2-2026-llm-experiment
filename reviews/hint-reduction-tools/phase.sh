#!/bin/bash
# usage: phase.sh <base.lisp> <name>  -- certify base, then each single-hint removal, in the container
set -e
BASE=$1; NAME=$2; R=/tmp/nohints-run/$NAME
rm -rf $R; mkdir -p $R/base
cp $BASE $R/base/solution.lisp
python3 -I /tmp/nohints-tools/hints.py variants $BASE $R/v >/dev/null
docker exec acl2-review rm -rf $R
docker cp $R acl2-review:$R
docker exec acl2-review bash -c "cd $R && /tmp/nohints-run/runone.sh $R/base && ls -d v/* | xargs -P 9 -n 1 /tmp/nohints-run/runone.sh > results.txt 2>&1; echo PASS: \$(sort -n results.txt | awk '\$2==\"PASS\"{printf \"%s,\", \$1}'); echo total \$(wc -l < results.txt)"
