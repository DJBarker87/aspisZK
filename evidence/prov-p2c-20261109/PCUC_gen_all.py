#!/usr/bin/env python3
"""PCUC_gen_all.py PREPARED.json [LABEL...]: probe-round generation for every pass of every prepared target (always --prune-fresh)."""
import json,subprocess,sys,os
from pathlib import Path
def cmd_for(key,r,ps,safe,rnd,prev,log=None,bk=None):
    m=r['module'];tag=ps['tag']
    c=['python3','-B','PCUC_gen_equalities.py','--partition','PCUC_PARTITION.json','--module',m,'--tag',tag,'--fresh-dir','inputs/fresh_'+safe,'--fresh-ns',ps['fresh_ns'][0],
       '--gate-source','inputs/gate_'+safe+'.lean','--out',f'PRVEq_{safe}.lean','--report',f'gen/PRVEq_{safe}.report{rnd}.json','--state-out',f'gen/PRVEq_{safe}.state{rnd}.json','--prune-fresh']
    if prev is not None: c+=['--state',f'gen/PRVEq_{safe}.state{prev}.json','--lean-log',log,'--bundle-offsets',f'gen/bundle_{bk}{prev}_offsets.json']
    if r['kind']=='Funs': c+=['--gate-types-source',ps['gate_types_path'] or 'inputs/gate_'+safe+'.lean']
    if r['kind']=='single':
        c+=['--gate-types-source',ps['gate_types_path'] or 'inputs/gate_'+safe+'.lean','--kind',r['view'].lower()]
    return c
if __name__=='__main__':
    prep=json.load(open(sys.argv[1]));only=sys.argv[2:];Path('gen').mkdir(exist_ok=True)
    for key,r in prep.items():
        if r['status']!='PREPARED' or (only and key not in only): continue
        for ps in r['passes']:
            safe=r['module'].replace('.','_')+ps['tag']
            p=subprocess.run(cmd_for(key,r,ps,safe,1,None),capture_output=True,text=True)
            print(safe,p.returncode,p.stderr.strip()[-300:],flush=True)
