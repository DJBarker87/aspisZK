#!/usr/bin/env python3
"""PCT_gen_all.py: run PCT_gen_equalities.py (probe round) for every module in a PCT_prepare output."""
import json,subprocess,sys
from pathlib import Path
prep=json.load(open(sys.argv[1]));only=sys.argv[2:]
Path('gen').mkdir(exist_ok=True)
for m,r in prep.items():
    if r['status']!='PREPARED' or (only and m not in only): continue
    safe=m.replace('.','_')
    cmd=['python3','-B','PCT_gen_equalities.py','--partition','PCT_PARTITION.json','--module',m,'--fresh-dir','inputs/fresh_'+safe,'--fresh-ns',r['fresh_ns'][0],
         '--gate-source','inputs/gate_'+safe+'.lean','--out',f'PRVEq_{safe}.lean','--report',f'gen/PRVEq_{safe}.report.json','--state-out',f'gen/PRVEq_{safe}.state1.json']
    if r['kind']=='Funs': cmd+=['--gate-types-source',r['gate_types_path'] or 'inputs/gate_'+safe+'.lean']
    if r['kind']=='single': cmd+=['--gate-types-source','inputs/gate_'+safe+'.lean']
    p=subprocess.run(cmd,capture_output=True,text=True)
    print(m,p.returncode,p.stdout.strip()[:200],p.stderr.strip()[-200:])
