from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(44,'NFV_Driver','lean',0),(45,'NFV_Driver','link',0),(46,'NFV_Driver','fixtures',0),(47,'NFV_Driver','final',0),(48,'NFV_Coherence','lean',0),(49,'NFV_Coherence','scan-link',0),(50,'NFV_Coherence','scan',1)]
for n,target,mode,expected in jobs:
 a=f'NFV_B{n:03}'
 assert not (E/a/'receipt.json').exists(),'no unchanged rerun'
 r=subprocess.run([sys.executable,str(E/'NFV_lean_run.py'),a,target,mode],capture_output=True,text=True)
 print(a,mode,'exit',r.returncode,flush=True)
 if r.returncode!=expected:print(r.stdout+r.stderr,flush=True);raise SystemExit('audit STOP; no resubmission')
subprocess.run([sys.executable,str(E/'NFV_collect_audit.py'),'NFV_B047','NFV_B050','NFV_B046'],check=True)
