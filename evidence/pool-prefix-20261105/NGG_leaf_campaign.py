from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for a,kind,mode in [(f'NGG_K{4+2*i+j:03d}',k,m) for i,k in enumerate(['loader','verifier','transport','count','payer','token']) for j,m in enumerate(['positive','negative'])]:
 r=subprocess.run([sys.executable,str(E/'NGG_leaf.py'),kind,mode],capture_output=True,text=True);assert r.returncode==0,r.stderr
 harness=r.stdout.strip()
 r=subprocess.run([sys.executable,str(E/'NGG_kani_run.py'),a,harness],capture_output=True,text=True)
 print(a,kind,mode,r.returncode,r.stdout.strip(),flush=True)
 receipt=E/a/'receipt.json'
 if not receipt.exists():print(r.stderr,flush=True);raise SystemExit('STOP unresolved or infrastructure')
 out=(E/a/'stdout.log').read_text()
 if 'TIMEOUT' in out.upper() or 'timed out' in out or 'memory' in out.lower() and 'killed' in out.lower():raise SystemExit('STOP review failed shape')
 if (mode=='positive' and r.returncode!=0) or (mode=='negative' and 'VERIFICATION:- FAILED' not in out):print(out[-2500:],flush=True);raise SystemExit('STOP unexpected verdict')
