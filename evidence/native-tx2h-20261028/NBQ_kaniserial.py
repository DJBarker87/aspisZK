from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);patch=sys.argv[2];crate=sys.argv[3]
for n,h in enumerate(sys.argv[4:],start):
 a=f'NBQ_K{n:03}'
 r=subprocess.run([sys.executable,str(E/'NBQ_kani.py'),a,crate,h,patch],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists(): print(r.stdout+r.stderr,flush=True);raise SystemExit('no receipt')
 x=json.loads(p.read_text());print(a,h,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status'] or r.returncode: print(r.stdout[-3000:]+r.stderr,flush=True);raise SystemExit('failed harness')
