from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for n,mode in enumerate(['left','right','size','slot','reply','branch','frame','copy','copy-negative'],4):
 a=f'NFJ_K{n:03}'
 subprocess.run([sys.executable,str(E/'NFJ_native.py'),mode],check=True)
 r=subprocess.run([sys.executable,str(E/'NFJ_kani_run.py'),a],capture_output=True,text=True)
 print(r.stdout[-2200:],flush=True)
 if not (E/a/'receipt.json').exists():raise SystemExit(r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 if rc['exit_status'] in [124,137] or 'timed out' in log.lower():raise SystemExit('family stopped for review; no unchanged rerun')
 assert rc['exit_status']==(0 if mode=='copy' else 1),(a,r.stdout,r.stderr)
 assert mode=='copy' or 'Failed Checks:' in log,(a,log[-2000:])
