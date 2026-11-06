"""Literal observation windows replace the timed-out low-region control."""
from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for n,slot,negative in [(32,0,False),(33,0,True),(34,1,False),(35,1,True),(36,2,False),(37,2,True)]:
 env=os.environ.copy();env['NJF_WINDOW']='high_pre';env['NJF_LITERAL']=str(slot)
 if negative:env['NJF_INVERT']='1';env['NJF_NATIVE_CFG']='NJF_mask_wrong'
 r=subprocess.run(['python3',str(E/'NJF_run.py'),f'NJF_K{n:03}','kani','weights::NJF_boundary::slice_boundary'],env=env)
 assert (E/f'NJF_K{n:03}/receipt.json').is_file(),'Missing receipt; stop, never resubmit'
 print(json.dumps(dict(attempt=f'NJF_K{n:03}',slot=slot,negative=negative,exit=r.returncode)),flush=True)
