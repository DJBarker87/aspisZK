import re,sys,difflib
def decls(path):
    t=open(path).read()
    return re.split(r'\n(?=(?:/--|@\[|def |theorem |abbrev |instance |structure |variable |end |namespace |axiom |opaque ))',t)
def name(p):
    m=re.search(r'(?:^|\n)(?:@\[[^\]]*\]\s*)*(def|abbrev|instance|theorem)\s+(?:\{[^}]*\}\s*)?([\w.]+)',p)
    return m.group(2) if m else None
def norm(s,ns):
    s=re.sub(r'/--.*?-/','',s,flags=re.S); return s.replace(ns,'NJS_Extract').strip()
fresh,gate,ns=sys.argv[1:4]; want=sys.argv[4:]
fn={name(p):p for p in decls(fresh) if name(p)}; gn={name(p):p for p in decls(gate) if name(p)}
for w in want:
    print('=====',w)
    a=norm(gn[w],'@@').splitlines(); b=norm(fn[w],ns).splitlines()
    for l in difflib.unified_diff(a,b,'gate','fresh',lineterm='',n=0): 
        if not l.startswith(('---','+++','@@')): print(l[:170])
