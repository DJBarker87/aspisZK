from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a in sys.argv[1:]:
 r=subprocess.run([sys.executable,str(E/'NKM_run.py'),a],capture_output=True,text=True)
 x=json.loads((E/(a+'.json')).read_text());rc=E/a/'receipt.json'
 print(r.stdout.strip() or (a+' client error'),flush=True)
 if not rc.exists():print(r.stderr[-500:],flush=True);break
 data=json.loads(rc.read_text());log=(E/a/'stdout.log').read_text()
 expected=x.get('negative_control',False)
 if expected:
  if r.returncode!=1 or 'VERIFICATION:- FAILED' not in log or 'CBMC timed out' in log or 'Timed out' in log:print('STOP negative not assertion failure',flush=True);break
 elif r.returncode:print('STOP positive failed; inspect before next scope',flush=True);break
