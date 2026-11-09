#!/usr/bin/env python3
"""PCUE_gen.py: driver for the generator. Labels = module + tag (+ pass index). Usage:
  PCUE_gen.py gen0 [LABEL...]                    probe-round generation (state1) for planned passes
  PCUE_gen.py ingest ROUND BK LOG [OFFS]         ingest a bundle Lean log: state<ROUND-1> -> state<ROUND>, regenerate PRVEq_<label>.lean
  PCUE_gen.py mkbundle BK ROUND                  build PRVEq_bundle_<BK><ROUND>.lean from gen/bundles.json[BK]
"""
import json,subprocess,sys,os,re
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;EV=H.parent
PLAN=json.load(open(H/'PCUE_PLAN.json'))
import PCUE_plan as PL
def label(m,ps): return m.replace('.','_')+ps['tag']
def passes():
    for m,r in PLAN.items():
        for ps in r['passes']: yield m,r,ps
def gate_files(m,r,ps):
    gt,gtt,origin=PL.gate_sources(m)
    # gate source files are referenced where they already exist in the repository; research-only sources are written to inputs/
    if origin.startswith('research:'):
        p=H/'inputs'/('gate_'+m.replace('.','_')+'.lean');p.write_text(gt);g=str(p)
        q=None
        if gtt is not None: q=H/'inputs'/('gatetypes_'+m.replace('.','_')+'.lean');q.write_text(gtt);q=str(q)
        return g,q
    g=str(EV/origin)
    q=None
    if gtt is not None:
        # types companion lives next to the gate source in P2a gate_src or P2d inputs
        if origin.startswith('prov-p2a'):
            ja=[j for j in PL.J.JOBS.values() if j['M']==m][0];q=str(EV/'prov-p2a-20261109/gate_src'/ja['types'])
        else: q=str(EV/origin.replace('/gate_','/gatetypes_'))
        if not Path(q).exists():   # sibling Types gate source (PCUE planner) not stored by P2a/P2d: write it next to the PCUE inputs
            p=H/'inputs'/('gatetypes_'+m.replace('.','_')+'.lean');p.write_text(gtt);q=str(p)
    return g,q
def cmd(m,r,ps,out,report,state_out=None,state=None,log=None,offs=None):
    lab=label(m,ps);g,q=gate_files(m,r,ps)
    c=['python3','-B',str(H/'PCUE_gen_equalities.py'),'--partition',str(EV/'prov-p2d-20261109/PCUD_PARTITION.json'),'--module',m,'--tag',ps['tag'],'--kind',ps['kind'].lower(),
       '--prune-fresh','--fresh-dir',str(EV/ps['fresh_dir']),'--fresh-ns',ps['fresh_ns'],'--gate-source',g,'--out',str(H/out),'--report',str(H/report)]
    if ps['kind']=='Funs': c+=['--gate-types-source',q or g]
    if ps.get('name_map'):
        nm=H/'gen'/('namemap_'+lab+'.json');nm.write_text(json.dumps(ps['name_map'],indent=1));c+=['--name-map',str(nm)]
    if m=='RPz7_FIp_NativeDots': c+=['--open-extra','FIo_Native']
    if state_out: c+=['--state-out',str(H/state_out)]
    if state: c+=['--state',str(H/state),'--lean-log',log]
    if offs: c+=['--bundle-offsets',str(H/offs)]
    return c
if __name__=='__main__':
    a=sys.argv[1]
    if a=='gen0':
        only=sys.argv[2:]
        for m,r,ps in passes():
            lab=label(m,ps)
            if only and lab not in only: continue
            p=subprocess.run(cmd(m,r,ps,f'PRVEq_{lab}.lean',f'gen/PRVEq_{lab}.report1.json',state_out=f'gen/PRVEq_{lab}.state1.json'),capture_output=True,text=True)
            print(lab,p.returncode,p.stdout.strip()[-160:],p.stderr.strip()[-300:],flush=True)
    elif a=='mkbundle':
        bk,rnd=sys.argv[2:4];ms=json.load(open(H/'gen/bundles.json'))[bk]
        subprocess.check_call(['python3','-B',str(H/'PCUE_bundle.py'),str(H/f'PRVEq_bundle_{bk}{rnd}.lean'),str(H/f'gen/bundle_{bk}{rnd}_offsets.json'),*[str(H/f'PRVEq_{l}.lean') for l in ms]])
    elif a=='ingest':
        rnd,bk,log=sys.argv[2:5];prev=int(rnd)-1;ms=json.load(open(H/'gen/bundles.json'))[bk]
        by={label(m,ps):(m,r,ps) for m,r,ps in passes()}
        for lab in ms:
            m,r,ps=by[lab]
            c=cmd(m,r,ps,f'PRVEq_{lab}.lean',f'gen/PRVEq_{lab}.report{rnd}.json',state_out=f'gen/PRVEq_{lab}.state{rnd}.json',state=f'gen/PRVEq_{lab}.state{prev}.json',log=log,offs=f'gen/bundle_{bk}{prev}_offsets.json')
            p=subprocess.run(c,capture_output=True,text=True);print(lab,p.returncode,p.stdout.strip()[-160:],p.stderr.strip()[-300:],flush=True)
