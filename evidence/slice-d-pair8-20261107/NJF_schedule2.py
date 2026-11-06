"""Sequential own window runner; no unchanged timed-out shape is retried."""
from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[(n,w,neg) for n,w,neg in [(12,'args',False),(13,'args',True),(14,'control',False),(15,'control',True),(16,'partial_args',False),(17,'partial_args',True),(18,'high_args',False),(19,'high_args',True),(20,'high_pre',False),(21,'high_pre',True),(22,'high_value',False),(23,'high_value',True),(24,'scratch',False),(25,'scratch',True),(26,'parts',False),(27,'parts',True)]]
for n,window,negative in jobs:
 env=os.environ.copy();env['NJF_WINDOW']=window
 if negative:env['NJF_INVERT']='1';env['NJF_NATIVE_CFG']='NJF_corrupt'
 r=subprocess.run(['python3',str(E/'NJF_run.py'),f'NJF_K{n:03}','kani','weights::NJF_boundary::slice_boundary'],env=env)
 if not (E/f'NJF_K{n:03}/receipt.json').is_file():raise SystemExit('Missing scope receipt; stop queue')
 rc=json.loads((E/f'NJF_K{n:03}/receipt.json').read_text())
 print(json.dumps(dict(attempt=rc['attempt'],window=window,negative=negative,exit=rc['exit_status'])),flush=True)
