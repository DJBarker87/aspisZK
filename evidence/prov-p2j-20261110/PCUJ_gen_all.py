#!/usr/bin/env python3
"""PCUJ_gen_all.py: from PCUJ_PLAN.json generate PRVEq_<M>_i<k>.lean per (module, pass) with PCUJ_gen_equalities.py.
Gate sources are read from git (research) into inputs/. Usage: PCUJ_gen_all.py [module ...]"""
import json,subprocess,sys,os,re
sys.dont_write_bytecode=True
H=os.path.dirname(os.path.abspath(__file__));EV=os.path.dirname(H);REPO=os.path.dirname(os.path.dirname(EV))
SET=os.environ.get('PCUJ_SET','wb');T=SET=='types';plan=json.load(open(H+'/PCUJ_PLAN.json'));prep=json.load(open(EV+'/prov-p5-20261109/gen/prepared2.json'))
only=sys.argv[1:];os.makedirs(H+'/inputs',exist_ok=True);os.makedirs(H+'/gen',exist_ok=True)
def gs(path,dest):
    t=subprocess.run(['git','-C',REPO,'show','research:'+path],capture_output=True,text=True)
    if t.returncode: return False
    open(dest,'w').write(t.stdout);return True
summary={}
for m,p in plan.items():
    if only and m not in only: continue
    if not p['passes']: continue
    safe=m.replace('.','_');gate=f'inputs/gate_{safe}.lean'
    if not os.path.exists(H+'/'+gate) and not gs(p['gate_source'],H+'/'+gate): print('NO GATE',m);continue
    kind='types' if (m.endswith('Types') or T) else 'funs'
    gt=gate
    pp=(prep.get(m) or {}).get('passes') or [{}]
    if kind=='funs' and pp[0].get('gate_types_path'):
        src=pp[0]['gate_types_path'];gt='inputs/gatetypes_'+safe+'.lean'
        if not os.path.exists(H+'/'+gt):
            if src.startswith('inputs/'): open(H+'/'+gt,'w').write(open(EV+'/prov-p5-20261109/'+src).read())
            else: gs(src,H+'/'+gt)
    for k,ps in enumerate(p['passes'],1):
        fd=EV+'/'+ps['fresh_dir']
        fname='Types.lean' if kind=='types' else 'Funs.lean'
        txt=open(fd+'/'+fname).read();ns=re.findall(r'(?m)^namespace\s+(\S+)',txt)[0]
        tag=f'_j{k}';out=f'PRVEq_{safe}{tag}.lean'
        of=f'gen/only_{safe}{tag}.json';json.dump(ps['only'],open(H+'/'+of,'w'))
        cmd=['python3','-B','PCUJ_gen_equalities.py','--module',m,'--tag',tag,'--fresh-dir',fd,'--fresh-ns',ns,'--gate-source',gate,'--gate-types-source',gt,
             '--out',out,'--report',f'gen/{safe}{tag}.report.json','--state-out',f'gen/{safe}{tag}.state.json','--prune-fresh']
        if kind=='funs': cmd+=['--only',of]
        if kind=='types' and not m.endswith('Types'): cmd+=['--kind','types']
        _gt=open(H+'/'+gate).read()
        if len(set(re.findall(r'(?m)^namespace\s+(\S+)',_gt)))>1: cmd+=['--gate-namespace',p['namespace']]
        r=subprocess.run(cmd,cwd=H,capture_output=True,text=True)
        summary[f'{m}{tag}']=dict(rc=r.returncode,config=ps['config'],fresh_dir=ps['fresh_dir'],n=len(ps['only']),err=r.stderr.strip()[-300:],out=r.stdout.strip()[-200:])
        print(m,tag,r.returncode,r.stderr.strip()[-200:].replace('\n',' | '))
json.dump(summary,open(H+'/gen/'+('PCUJ_GEN_SUMMARY.json'),'w'),indent=1)
