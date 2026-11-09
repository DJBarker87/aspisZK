#!/usr/bin/env python3
"""PCVA_p3gen.py IN_PRVEq.lean FRESH_FUNS.lean OUT_PRVEq_P3.lean [--no-vars]
Class NOMINAL (explicit opaque-call parameters): the P5 generator omitted the `variable (X_call_i : ...)` declarations of the
fresh Funs, so every fresh declaration that mentions an external call parameter was dropped. This tool
 (1) copies, byte for byte, every top-level `variable (...)` block of the fresh Funs into `namespace PRVFresh_<M>`,
 (2) turns every `PRV-FRESH-DROPPED` comment back into live text,
 (3) turns every `PRV-OBLIGATION` comment into the same S1/S2 theorem shape the P5 generator uses (rfl, then delta; rfl).
The theorem statement `@fresh.f = @gate.f` quantifies over the call parameters (they are leading arguments of both constants)."""
import sys,re
inp,fresh,out=sys.argv[1:4]
src=open(inp).read().split('\n')
fr=open(fresh).read().split('\n')
# variable blocks of fresh Funs: from 'variable (' up to the blank line that ends the block
vb=[];i=0
while i<len(fr):
    if fr[i].startswith('variable ('):
        j=i
        while fr[j].strip()!='': j+=1
        vb.append('\n'.join(fr[i:j])); i=j
    else: i+=1
# ---- callee tracking: fresh declaration bodies (live or dropped) in namespace PRVFresh_*; names of all equalities in the file
alltext='\n'.join(src)
blocks={};cur=None;ns_start=False
KW=re.compile(r'^(?:def|abbrev|opaque|instance|structure|inductive|axiom)\s+(\S+)')
inns=False
for l in src+['end PRVFresh_']:
    if l.startswith('namespace PRVFresh_'): inns=True;continue
    if l.startswith('end PRVFresh_'): inns=False;cur=None;continue
    if not inns: continue
    mk=KW.match(l)
    if mk: cur=mk.group(1);blocks[cur]=[l];continue
    if cur and l!='-/': blocks[cur].append(l)
eqnames=re.findall(r'^theorem (PRVEq\.\S+) :',alltext,re.M)+re.findall(r'PRV-OBLIGATION \([^)]*\): (\S+) :',alltext)
prefix=None
for e in eqnames:
    prefix=e.rsplit('.',0)[0];break
res=[];i=0;m=None;injected=False;proved_names=[];Mpref=None
while i<len(src):
    l=src[i]
    mm=re.match(r'namespace (PRVFresh_\S+)$',l)
    if mm: m=mm.group(1)
    if l.startswith('/- PRV-FRESH-DROPPED'):
        res.append('-- P3: previously dropped fresh declaration, now live'); i+=1
        while src[i]!='-/': res.append(src[i]); i+=1
        i+=1; continue
    if l.startswith('/- PRV-OBLIGATION'):
        mo=re.match(r'/- PRV-OBLIGATION \([^)]*\): (\S+) : (.*)$',l); name,stmt=mo.group(1),mo.group(2)
        i+=1
        while not src[i].rstrip().endswith('-/'): i+=1
        i+=1
        fn=re.match(r'@(\S+) = @(\S+)$',stmt.strip()); f,g=fn.group(1),fn.group(2)
        pf=f[1:] if f.startswith('@') else f
        short=g.split('.',1)[1] if False else None
        # bare declaration name relative to the fresh namespace
        bare=pf.split('.',1)[1]
        body='\n'.join(blocks.get(bare,[]))
        cal=[]
        for e in proved_names:
            n=e.split('.',3)[-1] if False else e
        for (en,nn) in proved_names:
            if nn!=bare and re.search(r'(?<![\w.])'+re.escape(nn)+r'(?![\w.])',body): cal.append(en)
        simp=f' try simp only [{", ".join(cal)}];' if cal else ''
        res.append(f'theorem {name} : {stmt} := by')
        res.append(f'  first | (trace "PRV-S1 {name}"; rfl) | (trace "PRV-S2 {name}"; delta {pf} {g};{simp} try rfl; done)')
        proved_names.append((name,bare))
        res.append(f'#print axioms {name}'); res.append('')
        continue
    mt=re.match(r'theorem (PRVEq\.\S+) : @(\S+) = @',l)
    if mt: proved_names.append((mt.group(1),mt.group(2).split('.',1)[1]))
    res.append(l)
    if '--no-vars' not in sys.argv and not injected and re.match(r'open \S+$',l) and m and res[-2].startswith('namespace '+m):
        for b in vb: res.append(''); res.append(b)
        injected=True
    i+=1
open(out,'w').write('\n'.join(res))
print('variable blocks',len(vb),'injected',injected)
