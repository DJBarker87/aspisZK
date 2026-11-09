#!/usr/bin/env python3
"""PCT_ingest.py ROUND BUNDLE LOGFILE: ingest a bundle Lean log (state<ROUND-1> -> state<ROUND>) for every module of the bundle."""
import json,subprocess,sys
rnd,bk,log=sys.argv[1:4];prev=int(rnd)-1
prep=json.load(open('gen/prepared2.json'));ms=json.load(open('gen/bundles.json'))[bk]
def info(label):
    for m,r in prep.items():
        for ps in r['passes']:
            if m.replace('.','_')+ps['tag']==label: return m,r,ps
for label in ms:
    m,r,ps=info(label);safe=label;tag=ps['tag']
    cmd=['python3','-B','PCT_gen_equalities.py','--partition','PCT_PARTITION.json','--module',m,'--tag',tag,'--fresh-dir','inputs/fresh_'+safe,'--fresh-ns',ps['fresh_ns'][0],
         '--gate-source','inputs/gate_'+safe+'.lean','--out',f'PRVEq_{safe}.lean','--report',f'gen/PRVEq_{safe}.report{rnd}.json','--state',f'gen/PRVEq_{safe}.state{prev}.json','--state-out',f'gen/PRVEq_{safe}.state{rnd}.json',
         '--lean-log',log,'--bundle-offsets',f'gen/bundle_{bk}{prev}_offsets.json']
    if r['kind']=='Funs': cmd+=['--gate-types-source',ps['gate_types_path'] or 'inputs/gate_'+safe+'.lean']
    if r['kind']=='single': cmd+=['--gate-types-source','inputs/gate_'+safe+'.lean']
    p=subprocess.run(cmd,capture_output=True,text=True)
    print(m,p.returncode,p.stdout.strip()[-150:],p.stderr.strip()[-200:])
