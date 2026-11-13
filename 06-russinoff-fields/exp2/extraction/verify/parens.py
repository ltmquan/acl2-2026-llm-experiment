import sys,re
txt=open(sys.argv[1]).read()
depth=0; i=0; line=1; sec=None
while i<len(txt):
    c=txt[i]
    if c=='\n':
        line+=1
        if txt.startswith(';; ----',i+1):
            print(line, 'depth', depth, txt[i+1:txt.find('\n',i+1)])
    if c==';':
        i=txt.find('\n',i); continue
    if c=='"':
        j=i+1
        while txt[j]!='"': j+= 2 if txt[j]=='\\' else 1
        line+=txt[i:j].count('\n'); i=j+1; continue
    if c=='#' and txt[i+1]=='|':
        j=txt.find('|#',i); line+=txt[i:j].count('\n'); i=j+2; continue
    if c=='(': depth+=1
    if c==')': depth-=1
    i+=1
print('final',depth)
