#!/usr/bin/env python3
"""PCQH_gen.py: driver for the generator over PCQH_PLAN.json. Labels = module + tag. Usage:
  PCQH_gen.py gen0 [LABEL...]                    probe-round generation (state1) for planned passes
  PCQH_gen.py ingest ROUND BK LOG                ingest a bundle Lean log: state<ROUND-1> -> state<ROUND>, regenerate PRVEq_<label>.lean
  PCQH_gen.py mkbundle BK ROUND                  build PRVEq_bundle_<BK><ROUND>.lean from gen/bundles.json[BK]
  PCQH_gen.py labels                             print all labels
"""
import json,subprocess,sys,os,re
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;EV=H.parent
PLAN=json.load(open(H/'PCQH_PLAN.json'))
SKIPDIV={'AspisR1AdapterReconstruct_Funs','S1NativeCompactModelV1'}  # PCUH change 2 (round-1 timeouts PCQH_L016/L017)
def label(m,ps): return m.replace('.','_')+ps['tag']
def passes():
    for m,r in PLAN.items():
        for ps in r['passes']: yield m,r,ps
def cmd(m,r,ps,out,report,state_out=None,state=None,log=None,offs=None):
    lab=label(m,ps)
    c=['python3','-B',str(H/'PCQH_gen_equalities.py'),'--module',m,'--tag',ps['tag'],'--kind',ps['kind'].lower(),
       '--prune-fresh','--fresh-dir',str(EV/ps['fresh_dir']),'--fresh-ns',ps['fresh_ns'],'--gate-source',str(EV/ps['gate']),'--out',str(H/out),'--report',str(H/report)]
    if ps['kind']=='Funs': c+=['--gate-types-source',str(EV/(ps['gate_types'] or ps['gate']))]
    if ps.get('name_map'):
        nm=H/'gen'/('namemap_'+lab+'.json');nm.write_text(json.dumps(ps['name_map'],indent=1));c+=['--name-map',str(nm)]
    for rn in ps.get('rename_fresh') or []: c+=['--rename-fresh',rn]
    for xg in ps.get('gate_extra') or []: c+=['--gate-extra-source',str(EV/xg)]
    of=H/'gen'/('only_'+lab+'.json');of.write_text(json.dumps(ps['only_fresh']));c+=['--only',str(of)]
    if lab in SKIPDIV: c+=['--skip-divergent']
    if ps.get('gate_namespace'): c+=['--gate-namespace',ps['gate_namespace']]
    for xi in ps.get('extra_import') or []: c+=['--extra-import',xi]
    for k in ('preamble','fresh_prelude','given'):
        if ps.get(k): c+=['--'+k.replace('_','-'),str(H/ps[k])]
    if state_out: c+=['--state-out',str(H/state_out)]
    if state: c+=['--state',str(H/state),'--lean-log',log]
    if offs: c+=['--bundle-offsets',str(H/offs)]
    return c
if __name__=='__main__':
    a=sys.argv[1];(H/'gen').mkdir(exist_ok=True)
    if a=='labels':
        for m,r,ps in passes(): print(label(m,ps))
    elif a=='gen0':
        only=sys.argv[2:]
        for m,r,ps in passes():
            lab=label(m,ps)
            if only and lab not in only: continue
            p=subprocess.run(cmd(m,r,ps,f'PRVEq_{lab}.lean',f'gen/PRVEq_{lab}.report1.json',state_out=f'gen/PRVEq_{lab}.state1.json'),capture_output=True,text=True)
            print(lab,p.returncode,p.stdout.strip()[-160:],p.stderr.strip()[-300:],flush=True)
    elif a=='mkbundle':
        bk,rnd=sys.argv[2:4];ms=json.load(open(H/'gen/bundles.json'))[bk]
        subprocess.check_call(['python3','-B',str(H/'PCQH_bundle.py'),str(H/f'PRVEq_bundle_{bk}{rnd}.lean'),str(H/f'gen/bundle_{bk}{rnd}_offsets.json'),*[str(H/f'PRVEq_{l}.lean') for l in ms]])
    elif a=='ingest':
        rnd,bk,log=sys.argv[2:5];prev=int(rnd)-1;ms=json.load(open(H/'gen/bundles.json'))[bk]
        by={label(m,ps):(m,r,ps) for m,r,ps in passes()}
        for lab in ms:
            m,r,ps=by[lab]
            c=cmd(m,r,ps,f'PRVEq_{lab}.lean',f'gen/PRVEq_{lab}.report{rnd}.json',state_out=f'gen/PRVEq_{lab}.state{rnd}.json',state=f'gen/PRVEq_{lab}.state{prev}.json',log=log,offs=f'gen/bundle_{bk}{prev}_offsets.json')
            p=subprocess.run(c,capture_output=True,text=True);print(lab,p.returncode,p.stdout.strip()[-160:],p.stderr.strip()[-300:],flush=True)
