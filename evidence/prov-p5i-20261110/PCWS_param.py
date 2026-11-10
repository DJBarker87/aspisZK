#!/usr/bin/env python3
"""PCWS_param.py: parametrize a fresh Aeneas Funs.lean the way a hand-adapted gate module is parametrized (PCWS-C classification: PARAMETRIC_OPS).
Gate modules such as NJS_Extract.Funs replace each external function/constant by `variable (NJS_call_k : T)`. This script
  (1) copies the gate's variable block into the fresh namespace,
  (2) replaces each fresh external name by its variable (mapping given in a JSON; each variable's type is compared textually with the fresh axiom's signature),
  (3) passes the variables a callee uses (taken from the GATE declaration of that callee) explicitly at each reference to the callee.
Nothing else is changed. The result is checked by the generated equalities (fresh_param.f = gate.f for every f)."""
import re,sys,json
sys.dont_write_bytecode=True
fresh,tmpl,gate,mapf,ns,out=sys.argv[1:7]
mp=json.load(open(mapf))   # {"NJS_call_0": "fresh.external.name", ...}
G=open(gate).read(); F=open(fresh).read(); T=open(tmpl).read()
SPLIT=r'\n(?=(?:/--|@\[|def |theorem |abbrev |instance |structure |variable |end |namespace |axiom |opaque ))'
gparts=re.split(SPLIT,G)
def dname(p):
    m=re.search(r'(?:^|\n)(?:@\[[^\]]*\]\s*)*(?:partial_fixpoint\s+)?(def|abbrev|instance)\s+(?:\{[^}]*\}\s*)?([\w.]+)',p); return m.group(2) if m else None
varblock=[p for p in gparts if p.lstrip().startswith('variable')]
gvars={}
for p in varblock:
    m=re.match(r'\s*variable \((NJS_call_\d+) : (.*)\)\s*$',p,re.S); assert m,p[:80]; gvars[m.group(1)]=m.group(2)
used={}
for p in gparts:
    n=dname(p)
    if n and not p.lstrip().startswith('variable'): used[n]=sorted(set(re.findall(r'NJS_call_\d+',re.sub(r'/--.*?-/','',p,flags=re.S))),key=lambda x:int(x.split('_')[2]))
# --- type check the mapping against the fresh template axioms
def squash(s): return re.sub(r'[\s,∀]','',s)
ax={}
for m in re.finditer(r'(?:^|\n)(?:@\[[^\n]*\n?[^\n]*\]\s*)?(?:axiom|opaque|def)\s+([\w.]+)\s*(.*?)(?=\n/--|\n@\[|\Z)',T,re.S):
    ax[m.group(1)]=m.group(2)
rep=[]
for v,n in mp.items():
    sig=ax.get(n)
    assert sig is not None,('external not in template',n)
    d=0;cut=None
    for i,ch in enumerate(sig):
        if ch in '({[': d+=1
        elif ch in ')}]': d-=1
        elif ch==':' and d==0: cut=i;break
    s1=squash(sig[:cut]+sig[cut+1:]) if cut is not None else squash(sig)
    s2=squash(gvars[v]); ok=(s1==s2)
    rep.append(dict(var=v,external=n,type_text_equal=bool(ok),fresh_sig=re.sub(r'\s+',' ',sig)[:300],gate_var=re.sub(r'\s+',' ',gvars[v])[:300]))
json.dump(rep,open(out+'.typecheck.json','w'),indent=1)
# --- transform
body=F
def tok(n): return r'(?<![\w.])'+re.escape(n)+r'(?![\w.])'
parts=re.split(SPLIT,body)
res=[]
for p in parts:
    head=p
    if re.match(r'\s*(?:/--|@\[|def |abbrev |instance )',p) or True:
        # mask the declared name
        dn=dname(p)
        mask='\x00DECL\x00'
        if dn: p=re.sub(r'((?:def|abbrev|instance)\s+(?:\{[^}]*\}\s*)?)'+re.escape(dn)+r'(?![\w.])',lambda m:m.group(1)+mask,p,count=1)
        for v,n in mp.items(): p=re.sub(tok(n),v,p)
        for g,vs in used.items():
            if vs and not g.startswith('NJS_call'): p=re.sub(tok(g),'('+g+' '+' '.join(vs)+')',p)
        if dn: p=p.replace(mask,dn)
    res.append(p)
txt='\n'.join(res)
blk='\n\n'.join('variable ('+k+' : '+v+')' for k,v in gvars.items())
txt=re.sub(r'(namespace '+re.escape(ns)+r'\n)',lambda m:m.group(1)+'\n'+blk+'\n',txt,count=1)
open(out,'w').write(txt)
print('wrote',out,'vars',len(gvars),'typechecks',sum(r['type_text_equal'] for r in rep),'of',len(rep))
