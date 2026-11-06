"""Serial remaining native pairs; no timeout rerun and no concurrent scopes."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a in ['NKB_K016','NKB_K011','NKB_K012','NKB_K013','NKB_K014']:
 x=json.loads((E/(a+'.json')).read_text());r=subprocess.run([sys.executable,str(E/'NKB_run.py'),a])
 if r.returncode!=(1 if x['expected_failure'] else 0):
  print(a+' STOP unexpected verdict; inspect before further launches',flush=True);raise SystemExit(2)
