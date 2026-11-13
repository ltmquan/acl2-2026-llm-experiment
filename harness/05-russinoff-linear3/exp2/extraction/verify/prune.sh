#!/bin/bash
T=<scratch>pad
W=<scratch>/prune; mkdir -p $W; cp <scratch>/given-russinoff-linear3/cert.acl2 $W/
cd $T; echo '[]' > drop.json
for k in $(python3 -c "import json;print(' '.join(reversed(json.load(open('order.json')))))"); do
  python3 -c "import json,sys;d=json.load(open('drop.json'));d.append('$k');json.dump(d,open('drop-try.json','w'))"
  (cd $T && python3 tools/gen.py drop-try.json >/dev/null && cp defs.lisp $W/defs.lisp)
  r=$($T/tools/try.sh $W | head -1)
  echo "$k $r"
  if [ "$r" = OK ]; then cp drop-try.json drop.json; fi
done
python3 tools/gen.py drop.json
