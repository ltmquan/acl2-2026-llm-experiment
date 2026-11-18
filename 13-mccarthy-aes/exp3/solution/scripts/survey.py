import json,sys,collections
d=json.load(open(sys.argv[1]))
table={}
bad=0
def expand(x):
    global bad
    if isinstance(x,dict):
        if len(x)==1 and 'Value' in x and isinstance(x['Value'],list) and len(x['Value'])==2 and isinstance(x['Value'][0],int):
            i,v=x['Value']; 
            if i in table: bad+=1
            v=expand(v); table[i]=v; return v
        if len(x)==1 and 'Deduplicated' in x:
            return table[x['Deduplicated']]
        return {k:expand(v) for k,v in x.items()}
    if isinstance(x,list): return [expand(v) for v in x]
    return x
t=expand(d)['translated']
print("dup ids",bad,"table",len(table))
C=collections.defaultdict(collections.Counter)
def tag(x):
    if isinstance(x,dict): return '{'+','.join(x.keys())+'}'
    return repr(x) if not isinstance(x,list) else 'list'
def kind(x): 
    if isinstance(x,dict): return list(x.keys())[0]
    return x
def place(p):
    k=p['kind']; C['place'][kind(k)]+=1
    if isinstance(k,dict) and 'Projection' in k:
        sub,proj=k['Projection']; C['proj'][json.dumps(proj)[:80] if kind(proj)!='Field' else 'Field:'+json.dumps(proj['Field'][0])[:60]]+=1; place(sub)
def operand(o):
    C['operand'][kind(o)]+=1
    if 'Copy' in o: place(o['Copy'][0] if isinstance(o['Copy'],list) else o['Copy'])
    elif 'Move' in o: place(o['Move'])
    elif 'Const' in o: C['const'][json.dumps(o['Const']['kind'])[:70] if 'kind' in o['Const'] else str(o['Const'])[:70]]+=1
def rvalue(r):
    k=kind(r); C['rvalue'][k]+=1
    v=r[k]
    if k=='Use': operand(v[0] if isinstance(v,list) else v)
    elif k=='BinaryOp': C['binop'][json.dumps(v[0])]+=1; operand(v[1]); operand(v[2])
    elif k=='UnaryOp': C['unop'][json.dumps(v[0])[:80]]+=1; operand(v[1])
    elif k=='Ref' : C['ref'][json.dumps({kk:vv for kk,vv in v.items() if kk!='place'} if isinstance(v,dict) else v[1:])[:150]]+=1
    elif k=='Aggregate': C['agg'][json.dumps(v[0])[:100]]+=1; [operand(o) for o in v[1]]
    else: C['rv-other'][json.dumps(r)[:200]]+=1
calls=collections.Counter()
for f in t['fun_decls']:
    if not f or not f['item_meta']['is_local']: continue
    b=f['body']['Unstructured']
    for blk in b['body']:
        for s in blk['statements']:
            k=kind(s['kind']); C['stmt'][k]+=1
            if k=='Assign': place(s['kind']['Assign'][0]); rvalue(s['kind']['Assign'][1])
        tk=blk['terminator']['kind']; C['term'][kind(tk)]+=1
        if kind(tk)=='Call':
            c=tk['Call']['call']; fn=c['func']
            C['callfn'][json.dumps(fn)[:60]]+=1
for k,v in C.items():
    print('==',k); 
    for a,b in v.most_common(60): print('  ',b,a)
