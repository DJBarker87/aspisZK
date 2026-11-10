#!/usr/bin/env python3
"""PCVC loop-bridge generator.  usage: gen_loops.py <P2g PRVEq file> <out> <fresh def name>... (callee-first order)
Writes base (P2g file with bridge inlined) + one `PRVC.Eq.<name>` theorem per loop def."""
import re,sys,hashlib
sys.path.insert(0,'.')
import mkbase
def build(src,out,names,bridge_inline=True,extra_done=()):
    tmp='/tmp/_b_'+hashlib.md5(src.encode()).hexdigest()+'.lean'
    mkbase.mk(src,tmp)
    base=open(tmp).read()
    ns=re.search(r'namespace (\w+)\nnamespace (PRVFresh_\w+)',base)
    G=ns.group(1)+'.'; F=G+ns.group(2)+'.'; NSF=G+ns.group(2)
    done=re.findall(r'^theorem (PRVEq\.\S+) :',base,re.M)+list(extra_done)
    txt=base.rstrip()+'\n'
    report={}
    for nm in names:
        t=one(base,nm,done,F,G,NSF)
        if t is None: report[nm]='NO SHAPE'; continue
        txt+=t; done.append('PRVC.Eq.'+nm); report[nm]='generated'
    open(out,'w').write(txt)
    return report
GNAME={}  # fresh def name -> gate def name (PCVD transport)
HOIST={}  # fresh loop name -> {param: gate-constant expr}
def one(base,name,done,F,G,NSF):
    m0=re.search(r'\ndef '+re.escape(name)+r'\n',base)
    if not m0: return None
    e0=base.find('\n\n',m0.end()); seg=base[m0.start():(e0+2 if e0>0 else len(base))]
    m=re.search(r'\ndef '+re.escape(name)+r'\n(.*?)(?:\n  | ):= do\n  loop\n    \(fun (.*?)\)\n    (.*?)\n\n',seg+'\n',re.S)
    if not m: return None
    hdr,lam,init=m.group(1),m.group(2),m.group(3).strip()
    lam=' '.join(lam.split())
    params=re.findall(r'\((\w+) :',hdr)
    hoist=HOIST.get(name,{})
    params_all=list(params); params=[p for p in params if p not in hoist]
    for hp,hq in hoist.items():
        lam=re.sub(r'(?<![\w.])'+hp+r'(?![\w.\'])','('+hq+')',lam)
    st=re.findall(r'\w+',init); k=len(st); n=len(params)
    if any(x not in params for x in st): return None
    def proj(i): return 'st' if k==1 else 'st'+'.2'*i+('.1' if i<k-1 else '')
    gst=' '.join((proj(st.index(p)) if p in st else p) for p in params)
    pat_in=('⟨'+', '.join(st)+'⟩') if k>1 else st[0]
    xs=' '.join(params)
    fa,ga=F+name,G+GNAME.get(name,name)
    fapp=fa+''.join(' ('+hoist[p]+')' for p in params_all if p in hoist)   # hoisted constant instantiated first (they lead the param list)
    assert all(p in hoist for p in params_all[:len(hoist)]),'hoisted params must lead'
    sc=''.join(', '+d for d in done)
    alts=[]
    for fixed in ([p for p in params if p not in st],[]):
        var=[p for p in params if p not in fixed]; nv=len(var)
        if nv==0: continue
        vs=' '.join(var); fx=' '.join(fixed)
        g2=' '.join((proj(st.index(p)) if p in st else p) for p in var)
        x2=' '.join((proj(st.index(p)).replace('st','x') if p in st else p) for p in var)
        alts.append(f'''    | (refine ({ga}.fixpoint_induct {fx} (fun f => ∀ {vs}, f {vs} ⊑ {fapp} {xs}) (PRVC.adm_le{nv} _) ?_) {vs}
       intro f hf {vs}
       refine PartialOrder.rel_trans (PRVC.rel_of_eq' (?_ : _ = PRVC.bs (fun {lam}) (fun st => f {g2}) ({init}))) ?_
       · rw [PRVC.bs_bind]
         simp only [{fa}.body{sc}]
         prv_peel
       · refine PartialOrder.rel_trans (PRVC.bs_mono (fun {lam}) _ (loop (fun {lam})) ?_ ({init})) (PRVC.rel_of_eq' (PRVC.loop_unfold (fun {lam}) ({init})).symm)
         intro x
         exact hf {x2})''')
    alts='\n'.join(alts)
    return f'''
open {NSF} in
theorem PRVC.Eq.{name} : @{fapp} = @{ga} := by
  delta {fa}
  try dsimp only
  funext {xs}
  refine PRVC.loop_eq_of_le _ (fun st => {ga} {gst}) ?_ ?_ ({init})
  · rintro {pat_in}
    refine PRVC.rel_of_eq' ?_
    show _ = {ga} {xs}
    rw [{ga}, PRVC.bs_bind]
    simp only [{fa}.body{sc}]
    prv_peel
  · rintro {pat_in}
    show {ga} {xs} ⊑ _
    first
{alts}
#print axioms PRVC.Eq.{name}
'''
if __name__=='__main__':
    src,out,*names=sys.argv[1:]
    print(build(src,out,names))
