"""Copy-specific controls: fail on copied words with all pointer assertions intact."""
from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for n,window in [(38,'args'),(39,'partial_args'),(40,'high_args')]:
 env=os.environ.copy();env['NJF_WINDOW']=window;env['NJF_INVERT']='1';env['NJF_NATIVE_CFG']='NJF_copy_wrong'
 r=subprocess.run(['python3',str(E/'NJF_run.py'),f'NJF_K{n:03}','kani','weights::NJF_boundary::slice_boundary'],env=env)
 assert (E/f'NJF_K{n:03}/receipt.json').is_file(),'Missing receipt; stop, never resubmit'
 print(json.dumps(dict(attempt=f'NJF_K{n:03}',window=window,negative=True,exit=r.returncode)),flush=True)
