from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[(10,'lean','NNI_OwnerStatements'),(11,'lean','NNI_HypothesisReview')]
for i,kind,target in jobs:
 a=f'NNI_L{i:03}';p=E/a/'receipt.json'
 if p.exists():
  assert json.loads(p.read_text())['exit_status']==0;continue
 r=subprocess.run([sys.executable,str(E/'NNI_run.py'),a,kind,target],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 print(a+' '+target+' '+str(r.returncode),flush=True)
 if r.returncode:print((r.stdout+r.stderr)[-1600:]);sys.exit(r.returncode)
