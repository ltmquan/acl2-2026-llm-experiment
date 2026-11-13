import re,sys,glob
clos=set(open('clos/closure.txt').read().split())
B='/home/user/acl2-exp/reference-books/pr-2103/books/workshops/2026/luu-medley-manolios/'
thms=set()
for f in glob.glob(B+'*.lisp'):
    for m in re.finditer(r"\((?:defrule|defruled|defthm|defthmd)\s+([^\s()]+)", open(f).read()):
        thms.add(m.group(1).upper())
for fn in sys.argv[1:]:
    t=open('authors/%s.cert.out'%fn).read()
    for m in re.finditer(r"Form:  \( (DEFUN|VERIFY-GUARDS|DEFTHM|DEFINE) ([^\s)]+).*?\nRules: (.*?)\nTime", t, re.S):
        kind,name,rules=m.groups()
        base=name
        if kind=='DEFTHM':
            mm=re.match(r".*-OF-(.*)$",name)
            if not (mm and mm.group(1) in clos): continue
        elif name not in clos: continue
        rs=set(r for r in re.findall(r"\(:[A-Z-]+ ([^\s()]+)\)",rules) if r in thms)
        if rs: print(fn,kind,name,sorted(rs))
