"""Same full common window, direct field projections instead of temporary arrays."""
from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for n,negative in [(42,False),(43,True)]:
 env=os.environ.copy();env['NJF_WINDOW']='partial_args'
 if negative:env['NJF_INVERT']='1';env['NJF_NATIVE_CFG']='NJF_copy_wrong'
 r=subprocess.run(['python3',str(E/'NJF_run.py'),f'NJF_K{n:03}','kani','weights::NJF_boundary::slice_boundary'],env=env)
 assert (E/f'NJF_K{n:03}/receipt.json').is_file(),'Missing receipt; stop, never resubmit'
 print(json.dumps(dict(attempt=f'NJF_K{n:03}',window='partial_args',negative=negative,exit=r.returncode)),flush=True)
