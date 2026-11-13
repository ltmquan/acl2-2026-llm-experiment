import re,sys
def forms(path):
    s=open(path).read()
    out=[];i=0;n=len(s);line=1
    while i<n:
        c=s[i]
        if c=='\n': line+=1;i+=1;continue
        if c==';':
            j=s.find('\n',i); i=n if j<0 else j; continue
        if s.startswith('#|',i):
            j=s.find('|#',i); line+=s.count('\n',i,j+2); i=j+2; continue
        if c.isspace(): i+=1;continue
        if c=='(':
            st=i;stl=line;d=0
            while True:
                c=s[i]
                if c=='\n': line+=1
                if c==';':
                    j=s.find('\n',i); i=j; continue
                if c=='"':
                    i+=1
                    while s[i]!='"':
                        if s[i]=='\\': i+=1
                        if s[i]=='\n': line+=1
                        i+=1
                elif c=='(': d+=1
                elif c==')':
                    d-=1
                    if d==0: i+=1;break
                i+=1
            txt=s[st:i]
            toks=re.findall(r"[^\s()]+",txt[:200])
            out.append((stl,toks[0].lower(),(toks[1].lower() if len(toks)>1 else ''),txt))
            continue
        i+=1
    return out
if __name__=='__main__':
    for l,k,nm,t in forms(sys.argv[1]): print(l,k,nm)
