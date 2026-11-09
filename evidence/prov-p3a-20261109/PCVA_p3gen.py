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
opts=dict(a.split('=',1) for a in sys.argv[4:] if a.startswith('--') and '=' in a)
CALL_MAP={}
if '--gate' in opts:
    # parameter instantiation (class NOMINAL): fresh external axiom / concrete callee  <->  gate `variable (X_call_k)`.
    import difflib
    def toks(pth):
        t=open(pth).read();t=re.sub(r'/-.*?-/','',t,flags=re.S);t=re.sub(r'--[^\n]*','',t)
        return re.findall(r"[A-Za-z_][\w'.]*#?\w*|\d+#?\w*|[^\sA-Za-z_\d]",t)
    a_=toks(fresh);b_=toks(opts['--gate']);pre=opts['--prefix']
    for op,i1,i2,j1,j2 in difflib.SequenceMatcher(None,a_,b_,autojunk=False).get_opcodes():
        if op=='replace' and i2-i1==1 and j2-j1==1 and b_[j1].startswith(pre): CALL_MAP[a_[i1]]=b_[j1]
src=open(inp).read().split('\n')
fr=open(opts.get('--gate',fresh)).read().split('\n')
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
DROPPED={}   # name -> renamed text
if CALL_MAP:
    k_=0
    while k_<len(src):
        if src[k_].startswith('/- PRV-FRESH-DROPPED'):
            k_+=1;bl=[]
            while src[k_]!='-/': bl.append(src[k_]);k_+=1
            j_='\n'.join(bl);md_=re.search(r'^(?:def|abbrev|impl_def|opaque)\s+(\S+)',j_,re.M)
            for kk,vv in sorted(CALL_MAP.items(),key=lambda kv:-len(kv[0])):
                j_=re.sub(r'(?<![\w.])'+re.escape(kk)+r'(?![\w.])',vv,j_)
            if md_ and md_.group(1) not in CALL_MAP: DROPPED[md_.group(1)]=j_
        k_+=1
BINDER={}
for b in vb:
    mb=re.match(r'variable \((\w+) :',b)
    if mb: BINDER[mb.group(1)]='('+b[len('variable ('):] if False else b[len('variable '):]
INSTS={}
PRE=opts.get('--prefix','@@')
def uvars(n_,seen=None):
    seen=seen if seen is not None else set()
    if n_ in seen: return set()
    seen.add(n_);t_=DROPPED.get(n_,'');u=set(re.findall(r'(?<![\w.])('+re.escape(PRE)+r'\d+)(?!\w)',t_))
    for m2 in DROPPED:
        if m2!=n_ and re.search(r'(?<![\w.])'+re.escape(m2)+r'(?![\w.])',t_): u|=uvars(m2,seen)
    return u
UV={}
if CALL_MAP:
    # impl_defs get explicit parameters (handled below); other defs reach their callees through explicit application
    for n_ in DROPPED:
        if not re.match(r'^impl_def',DROPPED[n_].lstrip().split('\n')[0]) and 'impl_def '+n_ not in DROPPED[n_]:
            u=uvars(n_)
            if u: UV[n_]=sorted(u,key=lambda x:int(x[len(PRE):]))
res=[];i=0;m=None;injected=False;proved_names=[];Mpref=None
while i<len(src):
    l=src[i]
    mm=re.match(r'namespace (PRVFresh_\S+)$',l)
    if mm: m=mm.group(1)
    if l.startswith('/- PRV-FRESH-DROPPED'):
        i+=1;blk=[]
        while src[i]!='-/': blk.append(src[i]); i+=1
        i+=1
        if CALL_MAP:
            joined='\n'.join(blk)
            md=re.search(r'^(?:def|abbrev|impl_def|opaque)\s+(\S+)',joined,re.M)
            if md and md.group(1) in CALL_MAP:
                res.append('-- P3: fresh definition '+md.group(1)+' is abstracted in the gate as parameter '+CALL_MAP[md.group(1)]+' (instantiation); not emitted'); continue
            for k,v in sorted(CALL_MAP.items(),key=lambda kv:-len(kv[0])):
                joined=re.sub(r'(?<![\w.])'+re.escape(k)+r'(?![\w.])',v,joined)
            mi=re.search(r'^impl_def\s+(\S+)',joined,re.M)
            if mi:
                nm=mi.group(1);used=[v for v in dict.fromkeys(re.findall(r'(?<![\w.])('+re.escape(opts['--prefix'])+r'\d+)(?!\w)',joined))]
                used.sort(key=lambda x:int(x[len(opts['--prefix']):]))
                INSTS[nm]=used
                body=re.sub(r'(?<![\w.])'+re.escape(nm)+r'(?![\w.])','('+nm+' '+' '.join(used)+')',joined)
                body=body.replace('impl_def ('+nm+' '+' '.join(used)+')','impl_def '+nm+' '+' '.join(BINDER[u] for u in used),1)
                joined=body
            else:
                for nm,used in INSTS.items():
                    joined=re.sub(r'(?<![\w.(])'+re.escape(nm)+r'(?![\w.])','('+nm+' '+' '.join(used)+')',joined)
                own=md.group(1) if md else None
                for nm,used in UV.items():
                    if nm==own: continue
                    # only when the callee needs variables that are not already instance arguments; skip the header line
                    joined=re.sub(r'(?<![\w.(])'+re.escape(nm)+r'(?![\w.])','('+nm+' '+' '.join(used)+')',joined)
                    joined=joined.replace('def ('+nm+' '+' '.join(used)+')','def '+nm,1)
            blk=joined.split('\n')
        res.append('-- P3: previously dropped fresh declaration, now live'); res.extend(blk)
        continue
    if l.startswith('/- PRV-OBLIGATION'):
        mo=re.match(r'/- PRV-OBLIGATION \([^)]*\): (\S+) : (.*)$',l); name,stmt=mo.group(1),mo.group(2)
        i+=1
        while not src[i].rstrip().endswith('-/'): i+=1
        i+=1
        fn=re.match(r'@(\S+) = @(\S+)$',stmt.strip()); f,g=fn.group(1),fn.group(2)
        pf=f[1:] if f.startswith('@') else f
        bare0=re.split(r'(?:^|\.)PRVFresh_[^.]*\.',pf,1)[-1]
        if bare0 in INSTS:
            vs=' '.join('c%d'%k for k in range(len(INSTS[bare0])))
            res.append(f'theorem {name} : {stmt} := by')
            res.append(f'  funext {vs}')
            res.append(f'  unfold {pf} {g}')
            res.append(f'  exact PRVEq_partialEq_ne_default _')
            res.append(f'#print axioms {name}'); res.append('')
            proved_names.append((name,bare0)); continue
        short=g.split('.',1)[1] if False else None
        # bare declaration name relative to the fresh namespace
        bare=re.split(r'(?:^|\.)PRVFresh_[^.]*\.',pf,1)[-1]
        body='\n'.join(blocks.get(bare,[]))
        cal=[]
        for e in proved_names:
            n=e.split('.',3)[-1] if False else e
        for (en,nn) in proved_names:
            if nn!=bare and re.search(r'(?<![\w.])'+re.escape(nn)+r'(?![\w.])',body): cal.append(en)
        simp=f' try simp only [{", ".join(cal)}];' if cal else ''
        if CALL_MAP and any(re.search(r'(?<![\w.])'+re.escape(nm)+r'(?![\w.])',body) for nm in INSTS):
            # gate parameter order puts the section variables consumed by instance constants first (observed on the compiled
            # constant NNG_verify_finish.r1_semantic.verify_finish); state the equality with the gate arguments permuted accordingly
            pre=opts['--prefix'];seen=set();stack=[bare];vars_=set()
            while stack:
                n_=stack.pop()
                if n_ in seen: continue
                seen.add(n_);bt='\n'.join(blocks.get(n_,[]))
                for k_,v_ in CALL_MAP.items():
                    if re.search(r'(?<![\w.])'+re.escape(k_)+r'(?![\w.])',bt): vars_.add(v_)
                vars_.update(re.findall(r'(?<![\w.])('+re.escape(pre)+r'\d+)(?!\w)',bt))
                for nm in INSTS:
                    if re.search(r'(?<![\w.])'+re.escape(nm)+r'(?![\w.])',bt): vars_.update(INSTS[nm])
                for n2 in blocks:
                    if n2!=n_ and re.search(r'(?<![\w.])'+re.escape(n2)+r'(?![\w.])',bt): stack.append(n2)
            ordv=sorted(vars_,key=lambda x:int(x[len(pre):]))
            instv=sorted({v for nm in INSTS for v in INSTS[nm] if v in vars_},key=lambda x:int(x[len(pre):]))
            gorder=instv+[v for v in ordv if v not in instv]
            res.append(f'theorem {name} : {stmt.split(" = ")[0]} = fun {" ".join(ordv)} => {stmt.split(" = ")[1]} {" ".join(gorder)} := by')
            res.append(f'  first | (trace "PRV-S1 {name}"; rfl) | (trace "PRV-S2 {name}"; delta {pf} {g};{simp} try rfl; done)')
            res.append(f'#print axioms {name}'); res.append('')
            proved_names.append((name,bare)); continue
        res.append(f'theorem {name} : {stmt} := by')
        if '--s2only' in sys.argv:
            res.append(f'  delta {pf} {g}')
            if cal: res.append(f'  simp only [{", ".join(cal)}]')
            res.append('  try rfl')
        else:
            res.append(f'  first | (trace "PRV-S1 {name}"; rfl) | (trace "PRV-S2 {name}"; delta {pf} {g};{simp} try rfl; done)')
        proved_names.append((name,bare))
        res.append(f'#print axioms {name}'); res.append('')
        continue
    mt=re.match(r'theorem (PRVEq\.\S+) : @(\S+) = @',l)
    if mt: proved_names.append((mt.group(1),re.split(r'(?:^|\.)PRVFresh_[^.]*\.',mt.group(2),1)[-1]))
    res.append(l)
    if CALL_MAP and l=='noncomputable section' and not any('PRVEq_partialEq_ne_default' in r for r in res):
        res.extend(['','theorem PRVEq_partialEq_ne_default {Self Rhs : Type} (c : Self → Rhs → Result Bool) :',
          '    ({ eq := c, ne := fun s o => core.cmp.PartialEq.ne.default c s o } : core.cmp.PartialEq Self Rhs) = { eq := c } := by',
          '  have h : (fun s o => core.cmp.PartialEq.ne.default c s o) = core.cmp.PartialEq.ne._default c := by',
          '    funext s o',
          '    simp only [core.cmp.PartialEq.ne.default, core.cmp.PartialEq.ne._default, id]',
          '    congr 1; funext b; cases b <;> rfl',
          '  rw [h]; rfl','#print axioms PRVEq_partialEq_ne_default',''])
    if '--no-vars' not in sys.argv and not injected and re.match(r'open \S+$',l) and m and res[-2].startswith('namespace '+m):
        for b in vb: res.append(''); res.append(b)
        injected=True
    i+=1
open(out,'w').write('\n'.join(res))
print('variable blocks',len(vb),'injected',injected)
