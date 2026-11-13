import json,re,sys
sys.path.insert(0,'')
it=json.load(open(sys.argv[1]))
TOK=re.compile(r"[^\s()'`,\"]+")
def strip(s):
    s=re.sub(r';[^\n]*','',s)
    s=re.sub(r'"(\\.|[^"\\])*"','',s)
    return s
def syms(s): return set(t.lower() for t in TOK.findall(strip(s)) if not t.startswith(':'))
defmap={}
for i in it:
    for d in i['defs']:
        if i['head']=='encapsulate' and i['inenc']: continue
        defmap.setdefault(d,i)
def target(name):
    for i in it:
        if i['head'] in('defthm','local-defthm') and i['name']==name: return i
tnames=sys.argv[2:]
need=[];seen=set()
work=[]
for tn in tnames:
    t=target(tn); print("TARGET",tn,t['book'],t['line'])
    txt=t['text']; txt=txt.split(':hints')[0]
    work+=list(syms(txt))
while work:
    s=work.pop()
    if s in seen or s not in defmap: continue
    seen.add(s); i=defmap[s]
    if id(i) not in [id(x) for x in need]:
        need.append(i)
        txt=i['text']
        work+=list(syms(txt))
order={(i['book'],i['line']):k for k,i in enumerate(it)}
need.sort(key=lambda i:order[(i['book'],i['line'])])
import collections
print(collections.Counter(i['book'] for i in need), len(need))
for i in need: print(i['book'],i['line'],i['head'],i['defs'])
json.dump([(i['book'],i['line']) for i in need],open('need.json','w'))
