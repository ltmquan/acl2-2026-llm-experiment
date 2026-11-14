# Reference (Python) model of the ACL2 importer's sharing expansion (development aid;
# the ACL2 importer in /work/mir/import-json.lisp implements the same rules).
# Charon's deduplicated serialization keeps one sharing table per hash-consed type:
#   {"Value": [id, X]} defines id in that table, {"Deduplicated": id} refers back,
#   {"Untagged": X} is an unshared occurrence.
# The table is determined by the JSON context (field name, list position).
import json,sys
TY_KEYS={'ty','types','inputs','output','Lub','Alias','SizeOf','AlignOf','GenericType',
         'InheritFrom','self_ty'}
TREF_KEYS={'Copy','ParentClause','TraitType','elem_is_copy','elem_is_sized','trait_ref'}
CEXPR_KEYS={'Const','Constant','Length','const_generics','count','ptr_metadata','branches'}
SIZE_KEYS={'AtLeast','GuaranteedAlignment','Max','chosen','target_align','guarantee','base','Plus','AlignTo'}
PRED_KEYS={'And','Or','inhabited'}
def category(key,idx,sibs):
    if key=='span': return 'span'
    if key=='#cexpr': return 'ty' if idx==1 else 'none'
    if key=='skip_binder': return 'ty' if 'params' in sibs else 'tref'
    if key=='value':
        return 'ty' if 'implied_trait_refs' in sibs else 'cexpr'
    if key=='Ref': return 'ty' if idx==1 else 'none'
    if key=='RawPtr': return 'ty' if idx==0 else 'none'
    if key=='Unsize': return 'ty' if idx==0 else 'none'
    if key=='Array': return {0:'ty',1:'cexpr',2:'tref'}.get(idx,'none')
    if key=='Slice': return {0:'ty',1:'tref'}.get(idx,'none')
    if key in ('Const','Constant') and idx==1: return 'ty'
    if key=='Copy' and idx==1: return 'tref'
    if key in TY_KEYS: return 'ty'
    if key in TREF_KEYS: return 'tref'
    if key in CEXPR_KEYS: return 'cexpr'
    if key in SIZE_KEYS: return 'size'
    if key in PRED_KEYS: return 'pred'
    return 'none'
def expand(doc):
    tabs={}
    def go(x,key,idx,sibs):
        if isinstance(x,dict):
            if len(x)==1 and 'Untagged' in x:
                return go(x['Untagged'],key,idx,sibs)
            if len(x)==1 and 'Value' in x and isinstance(x['Value'],list) and len(x['Value'])==2 and isinstance(x['Value'][0],int):
                c=category(key,idx,sibs); assert c!='none',(key,idx)
                v=go(x['Value'][1],'#'+c,None,sibs); tabs[(c,x['Value'][0])]=v; return v
            if len(x)==1 and 'Deduplicated' in x:
                c=category(key,idx,sibs); assert c!='none',(key,idx)
                return tabs[(c,x['Deduplicated'])]
            s=set(x.keys())
            return {k:go(v,k,None,s) for k,v in x.items()}
        if isinstance(x,list):
            return [go(v,key,i,sibs) for i,v in enumerate(x)]
        return x
    return go(doc,'',None,set())
if __name__=='__main__':
    t=expand(json.load(open(sys.argv[1])))
    json.dump(t,open(sys.argv[2],'w'))
