"""Sequential own window runner; no unchanged timed-out shape is retried."""
from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[(3,'control',True),(4,'args',False),(5,'args',True),(6,'scratch',False),(7,'scratch',True),(8,'parts',False),(9,'parts',True),(10,'shared',False),(11,'shared',True)]
for n,window,negative in jobs:
 env=os.environ.copy();env['NJF_WINDOW']=window
 if negative:env['NJF_INVERT']='1';env['NJF_NATIVE_CFG']='NJF_corrupt'
 r=subprocess.run(['python3',str(E/'NJF_run.py'),f'NJF_K{n:03}','kani','weights::NJF_boundary::slice_boundary'],env=env)
 if not (E/f'NJF_K{n:03}/receipt.json').is_file():raise SystemExit('Missing scope receipt; stop queue')
 rc=json.loads((E/f'NJF_K{n:03}/receipt.json').read_text())
 print(json.dumps(dict(attempt=rc['attempt'],window=window,negative=negative,exit=rc['exit_status'])),flush=True)
