import json,sys
sys.path.insert(0,sys.argv[1])
from extract import strip_comments
it=json.load(open(sys.argv[2])); need=[tuple(x) for x in json.load(open(sys.argv[3]))]
by={(i['book'],i['line']):i for i in it}
out=['(in-package "ACL2")','(include-book "misc/records" :dir :system)']
for k in need: out.append(strip_comments(by[k]['text']))
open(sys.argv[4],'w').write('\n\n'.join(out)+'\n')
