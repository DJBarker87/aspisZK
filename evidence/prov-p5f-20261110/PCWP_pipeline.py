#!/usr/bin/env python3
"""PCWP_pipeline.py: probe/final generation of a fresh = gate equality file for one FIq gate module whose closure reaches
core::array::from_fn (HM-D).  probe: generator output (compile it once).  final LOG: ingest the probe log, add PRVC loop
bridges (gen_loops), then re-state every remaining obligation by the generator's stage-2 shape with all earlier equalities and the HM-D
unfolding in the simp set; the fresh external core.array.from_fn is the HM-D model (hmd_prelude.lean)."""
import sys,re,json,subprocess,os
sys.dont_write_bytecode=True
mode,M,tag,fresh,ns,only=sys.argv[1:7]
rest=sys.argv[7:]
loops=[x for x in rest if not x.startswith('--') and not x.startswith('LOG=')]
log=[x[4:] for x in rest if x.startswith('LOG=')]
n=int(M.replace('RPu_FIq_Native','')) if M[-2:].isdigit() else 0
extras=[f'inputs/RPu_FIq_Native{i:02d}.lean' for i in range(1,n) if os.path.exists(f'inputs/RPu_FIq_Native{i:02d}.lean')]
lab=f'{M}_{tag}'
gen=['python3','-B','PCWP_gen_equalities.py','--module',M,'--fresh-dir',fresh,'--fresh-ns',ns,'--gate-source',f'inputs/{M}.lean','--gate-types-source',f'inputs/{M}.lean',
 '--rename-fresh','aspis_core.=','--rename-fresh','aspis_statement.=','--kind','funs','--only',only,'--fresh-prelude','inputs/hmd_prelude.lean','--tag','_'+tag]
for e in extras: gen+=['--gate-extra-source',e]
gen+=['--prune-fresh','--out',f'PRVEq_{lab}.lean']
FQ=f'FIq_Native.PRVFresh_{lab}'; P=f'PRVEq.{lab}'
if mode=='probe':
    r=subprocess.run(gen+['--report',f'gen/{tag}.report.json','--state-out',f'gen/{tag}.state.json'],capture_output=True,text=True);print(r.stdout[-300:],r.stderr[-300:])
else:
    r=subprocess.run(gen+['--report',f'gen/{tag}.report2.json','--state',f'gen/{tag}.state.json','--lean-log',log[0],'--state-out',f'gen/{tag}.state2.json'],capture_output=True,text=True);print(r.stdout[-300:],r.stderr[-300:])
    src=open(f'PRVEq_{lab}.lean').read()
    import mkbase,gen_loops
    base=f'PRVEq_{lab}_b.lean'
    mkbase.mk(f'PRVEq_{lab}.lean',base)
    bs=open(base).read()
    # ordered items of the generator's output: kept theorems and obligation comments
    items=[]
    for m in re.finditer(r'(?:^theorem (PRVEq\.\S+) : @(\S+) = @(\S+) :=|^/- PRV-OBLIGATION \((?:transport-needed|semantic); P3\): (PRVEq\.\S+) : @(\S+) = @(\S+)\n)',src,re.M):
        g=m.groups()
        items.append((g[0] or g[3],g[1] or g[4],g[2] or g[5],'thm' if g[0] else 'obl'))
    first=next(i for i,x in enumerate(items) if x[3]=='obl')
    keep=items[:first]; redo=items[first:]
    # cut the base after the #print axioms line of the last kept theorem
    cut=len(bs)
    if keep:
        k=bs.index('#print axioms '+keep[-1][0]+'\n'); cut=bs.index('\n',k)+1
    else:
        cut=bs.index('theorem '+items[0][0]); cut=bs.rfind('set_option maxHeartbeats',0,cut)
    head=bs[:cut].rstrip()+'\n'
    ns_=re.search(r'namespace (\w+)\nnamespace (PRVFresh_\w+)',bs)
    G=ns_.group(1)+'.'; F=G+ns_.group(2)+'.'; NSF=G+ns_.group(2)
    unf=[f'{FQ}.core.array.from_fn','FIq_Native.array_from_fn_copy']
    # topological order of the redo items by references in the fresh text (a loop may need closure instances and vice versa)
    names={x[0][len(P)+1:]:x for x in redo}
    def block(nm):
        m=re.search(r'\ndef\s+'+re.escape(nm)+r'(?=[\s(])',bs)
        if not m: return ''
        e=bs.find('\n\n',m.end()); return bs[m.start():(e if e>0 else len(bs))]
    deps={}
    for nm in names:
        blk=block(nm); blk2=block(nm+'.body') if True else ''
        deps[nm]=[o for o in names if o!=nm and re.search(r'(?<![\w.])'+re.escape(o)+r'(?![\w.])',blk+blk2)]
    order=[];seen=set()
    def visit(nm,stack=()):
        if nm in seen or nm in stack: return
        for d in deps[nm]: visit(d,stack+(nm,))
        seen.add(nm);order.append(nm)
    for nm in names: visit(nm)
    redo=[names[nm] for nm in order]
    done=[x[0] for x in keep]
    t=''
    nloop=0;nplain=0
    for en,fr,ga,kind in redo:
        short=en[len(P)+1:]
        if short in loops:
            lt=gen_loops.one(bs,short,done,F,G,NSF)
            if lt is not None:
                lt=re.sub(r'simp only \[(FIq_Native\.PRVFresh_\w+\.\S+?\.body)',lambda m:'simp only ['+', '.join(unf)+', '+m.group(1),lt)
                t+=lt;done.append('PRVC.Eq.'+short);nloop+=1;continue
        t+=f'''
set_option maxHeartbeats 200000 in
theorem {en} : @{fr} = @{ga} := by
  first
  | rfl
  | (delta {fr} {ga}
     try simp only [{', '.join(unf+done)}]
     try rfl
     done)
#print axioms {en}
'''
        done.append(en);nplain+=1
    s=head+t
    print('kept',len(keep),'loops',nloop,'plain',nplain)
    s=s.replace('set_option maxHeartbeats 1000000','set_option maxHeartbeats 200000',1)
    a=s.index('namespace PRVFresh_'); a=s.rfind('\n',0,s.rfind('namespace FIq_Native',0,a))+1
    s=s[:a]+'set_option maxHeartbeats 1000000  -- inlined Aeneas emission only (default header)\n'+s[a:]
    b=s.index('end PRVFresh_'); b=s.index('\n',s.index('end FIq_Native',b))+1
    s=s[:b]+'set_option maxHeartbeats 200000  -- every theorem below\n'+s[b:]
    open(f'PRVEq_{lab}_c.lean','w').write(s)
    
