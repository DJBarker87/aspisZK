#!/usr/bin/env python3
"""PCVK_ generator: from one Aeneas emission (Funs.lean + FunsExternal_Template.lean) produce the 'fresh text with externals as fields of Ext'.
usage: PCVK_gen_ext.py EMISSION_RAW_DIR NAMESPACE ROOTS(comma) OUT.fragment [EXCLUDE(comma, names left to the gate library, e.g. core.result.Result.map_err)]
Emits: structure Ext (only the externals that the reachable fresh blocks mention), and the reachable blocks with each external replaced by x.<field>
and each block that (transitively) mentions x given an explicit (x : Ext) parameter, call sites rewritten (NAME x).
Also writes OUT.fields.json: field -> original external name (for the hand Bound table)."""
import re,sys,json
raw,ns,roots,out=sys.argv[1:5]
excl=set(x for x in (sys.argv[5] if len(sys.argv)>5 else '').split(',') if x)
roots=roots.split(',')
funs=open(raw+'/Funs.lean').read(); tpl=open(raw+'/FunsExternal_Template.lean').read()
def split_blocks(t):
    return re.split(r'\n(?=/--)',t)
# ---- externals from the template
ext={}
for b in split_blocks(tpl):
    m=re.search(r'\naxiom\s+(\S+)',b)
    if not m: continue
    name=m.group(1)
    rest=b[m.end():]
    if name.endswith(':') : pass
    # binder groups
    i=0;groups=[]
    def skip_ws(i):
        while i<len(rest) and rest[i].isspace(): i+=1
        return i
    i=skip_ws(0)
    # name may be on next line (axiom\n  name) handled by regex \s+
    while i<len(rest) and rest[i] in '({':
        op=rest[i];cl={'(':')','{':'}'}[op];d=0;j=i
        while True:
            if rest[j] in '({[': d+=1
            elif rest[j] in ')}]': d-=1
            j+=1
            if d==0: break
        groups.append(rest[i:j]);i=skip_ws(j)
    assert rest[i]==':',(name,rest[i:i+40])
    ty=re.sub(r'\s+',' ',rest[i+1:]).strip()
    ty=re.sub(r'/--.*$','',ty).strip()
    ext[name]=('∀ '+' '.join(groups)+', ' if groups else '')+ty
# ---- blocks of Funs
body=funs[funs.index('namespace'):]
body=body[body.index('\n')+1:body.rindex('end ')]
blocks=[b.strip('\n') for b in split_blocks(body) if b.strip()]
def defname(b):
    m=re.search(r'(?:^|\n)(?:@\[[^\]]*\]\s*)*def\s+(\S+)',b,re.S)
    return m.group(1) if m else None
names={defname(b):b for b in blocks if defname(b)}
# reachable
need=set();stack=list(roots)
while stack:
    n=stack.pop()
    if n in need: continue
    need.add(n)
    for m in names:
        if m not in need and m!=n and re.search(r'(?<![\w.])'+re.escape(m)+r'(?![\w.])',names[n]): stack.append(m)
sel=[b for b in blocks if defname(b) in need]
# ---- externals used
def ident(n): return re.sub(r'[^A-Za-z0-9]','_',n).strip('_')
used={}
text='\n\n'.join(sel)
for n in sorted(ext,key=len,reverse=True):
    if n in excl: continue
    if re.search(r'(?<![\w.])'+re.escape(n)+r'(?![\w.])',text):
        used[n]=ident(n)
# longest-first replacement avoiding double replacement
def repl_ext(t):
    for n in sorted(used,key=len,reverse=True):
        t=re.sub(r'(?<![\w.])'+re.escape(n)+r'(?![\w.])','x.'+used[n],t)
    return t
sel2=[]
for b in sel:
    # keep doc comment untouched
    m=re.match(r'(/--.*?-/\n)',b,re.S)
    doc=m.group(1) if m else ''
    sel2.append((doc,repl_ext(b[len(doc):])))
# ---- which blocks need x
needx=set()
chg=True
while chg:
    chg=False
    for (doc,b) in sel2:
        n=defname(b)
        if n in needx: continue
        if re.search(r'(?<![\w.])x\.',b) or any(re.search(r'(?<![\w.])'+re.escape(m)+r'(?![\w.])',b.split(':=',1)[-1]) for m in needx if m!=n):
            needx.add(n);chg=True
res=[]
for (doc,b) in sel2:
    n=defname(b)
    for m in needx:
        if m==n: continue
        b=re.sub(r'(?<![\w.])'+re.escape(m)+r'(?![\w.])','('+m+' x)',b)
    if n in needx:
        b=re.sub(r'(def\s+'+re.escape(n)+r')',r'\1 (x : Ext)',b,count=1)
    res.append(b)
stru='structure Ext where\n'+'\n'.join('  %s : %s'%(v,ext[k]) for k,v in used.items())+'\n'
open(out,'w').write(stru+'\n'+'\n\n'.join(res)+'\n')
json.dump(dict(fields={v:k for k,v in used.items()},needx=sorted(needx),blocks=sorted(need)),open(out+'.json','w'),indent=1)
print(len(used),'externals',len(sel),'blocks',len(needx),'with x')
