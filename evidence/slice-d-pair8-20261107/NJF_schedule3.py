"""Split the timed-out high-pre-state observation into exhaustive slot windows."""
from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for n,region,negative in [(28,'slot_low',False),(29,'slot_low',True),(30,'slot_high',False),(31,'slot_high',True)]:
 env=os.environ.copy();env['NJF_WINDOW']='high_pre';env['NJF_SELECT']=region
 if negative:env['NJF_INVERT']='1';env['NJF_NATIVE_CFG']='NJF_mask_wrong'
 r=subprocess.run(['python3',str(E/'NJF_run.py'),f'NJF_K{n:03}','kani','weights::NJF_boundary::slice_boundary'],env=env)
 assert (E/f'NJF_K{n:03}/receipt.json').is_file(),'Missing receipt; stop, never resubmit'
 print(json.dumps(dict(attempt=f'NJF_K{n:03}',region=region,negative=negative,exit=r.returncode)),flush=True)
