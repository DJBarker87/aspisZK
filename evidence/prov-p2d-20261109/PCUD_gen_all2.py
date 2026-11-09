#!/usr/bin/env python3
"""PCUD_gen_all2.py PREPARED2.json: probe-round generation for every pass of every module."""
import json,subprocess,sys,os
PR=set(json.load(open('gen/pruned_labels.json'))) if os.path.exists('gen/pruned_labels.json') else set()
from pathlib import Path
prep=json.load(open(sys.argv[1]));only=sys.argv[2:];Path('gen').mkdir(exist_ok=True)
for m,r in prep.items():
    if r['status']!='PREPARED' or (only and m not in only): continue
    for ps in r['passes']:
        tag=ps['tag'];safe=m.replace('.','_')+tag
        if os.environ.get('LABELS') and safe not in os.environ['LABELS'].split(','): continue
        cmd=['python3','-B','PCUD_gen_equalities.py','--partition','PCUD_PARTITION.json','--module',m,'--tag',tag,'--fresh-dir','inputs/fresh_'+safe,'--fresh-ns',ps['fresh_ns'][0],
             '--gate-source','inputs/gate_'+safe+'.lean','--out',f'PRVEq_{safe}.lean','--report',f'gen/PRVEq_{safe}.report1.json','--state-out',f'gen/PRVEq_{safe}.state1.json']
        if safe in PR: cmd+=['--prune-fresh']
        if r['kind']=='Funs': cmd+=['--gate-types-source',ps['gate_types_path'] or 'inputs/gate_'+safe+'.lean']
        if r['kind']=='single': cmd+=['--gate-types-source','inputs/gate_'+safe+'.lean']
        p=subprocess.run(cmd,capture_output=True,text=True)
        print(safe,p.returncode,p.stderr.strip()[-200:])
