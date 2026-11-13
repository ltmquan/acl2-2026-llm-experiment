# Extract top-level forms from the authors' books and compute the transitive
# definition closure needed by the target statements.
import re, sys, json
BOOKS = ["model","scan","basic","good_state_inv","recovery_inv","channel_equivalence","cut_meta_inv","local_swap","global_reorder"]
SRC = sys.argv[1] if len(sys.argv)>1 else None

def forms(text):
    i=0; n=len(text); out=[]
    depth=0; start=None
    while i<n:
        c=text[i]
        if c==';':
            j=text.find('\n',i); i = n if j<0 else j; continue
        if text.startswith('#|',i):
            d=1; i+=2
            while d>0:
                if text.startswith('|#',i): d-=1; i+=2
                elif text.startswith('#|',i): d+=1; i+=2
                else: i+=1
            continue
        if c=='"':
            i+=1
            while text[i]!='"':
                if text[i]=='\\': i+=1
                i+=1
            i+=1; continue
        if text.startswith('#\\',i): i+=3; continue
        if c=='|':
            j=text.find('|',i+1); i=j+1; continue
        if c=='(':
            if depth==0: start=i
            depth+=1
        elif c==')':
            depth-=1
            if depth==0: out.append((start,i+1))
        i+=1
    return out

def strip_comments(s):
    # remove ; comments outside strings, and #| |#
    res=[]; i=0; n=len(s)
    while i<n:
        c=s[i]
        if c==';':
            j=s.find('\n',i); i = n if j<0 else j; continue
        if s.startswith('#|',i):
            d=1;i+=2
            while d>0:
                if s.startswith('|#',i): d-=1;i+=2
                elif s.startswith('#|',i): d+=1;i+=2
                else: i+=1
            continue
        if c=='"':
            j=i+1
            while s[j]!='"':
                if s[j]=='\\': j+=1
                j+=1
            res.append(s[i:j+1]); i=j+1; continue
        if s.startswith('#\\',i): res.append(s[i:i+3]); i+=3; continue
        res.append(c); i+=1
    out=''.join(res)
    # drop trailing whitespace and blank lines
    lines=[l.rstrip() for l in out.split('\n')]
    lines=[l for l in lines if l.strip()]
    return '\n'.join(lines)

TOK=re.compile(r"[^\s()'`,\"]+")
def syms(s):
    s=re.sub(r'"(\\.|[^"\\])*"','',s)
    return set(t.lower() for t in TOK.findall(s) if not t.startswith(':') and not t.startswith('#'))

def flat(t):
    for (a,e) in forms(t):
        txt=t[a:e]
        if re.match(r"\(encapsulate\s*(\(\s*\)|nil)",txt,re.I):
            inner=re.match(r"\(encapsulate\s*(\(\s*\)|nil)",txt,re.I).end()
            for (a2,e2) in forms(t[a+inner:e-1]):
                yield (a+inner+a2,a+inner+e2,True)
        else: yield (a,e,False)
if __name__=='__main__':
  items=[]
  for b in BOOKS:
      t=open(f"{SRC}/{b}.lisp").read()
      for (a,e,inenc) in flat(t):
          txt=t[a:e]; line=t.count('\n',0,a)+1
          m=re.match(r"\(\s*([^\s()]+)\s*(\S*)",txt)
          head=m.group(1).lower(); name=m.group(2).lower().strip('()')
          defs=[]
          if head in ("defun","defmacro","defstub","defconst","defund"): defs=[name]
          elif head=="encapsulate":
              sig=txt[len("(encapsulate"):]
              defs=[x.lower() for x in re.findall(r"\(\(\s*([^\s()]+)",sig)]
              # only signatures: those in first arg list; also non-local defuns inside? check later
          elif head=="mutual-recursion":
              defs=[x.lower() for x in re.findall(r"\(defun\s+(\S+)",txt)]
          items.append(dict(inenc=inenc,book=b,line=line,head=head,name=name,defs=defs,text=txt))
  json.dump(items,open(sys.argv[2],"w"))
