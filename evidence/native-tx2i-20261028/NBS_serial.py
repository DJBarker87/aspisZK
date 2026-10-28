from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
first=int(sys.argv[1]);patch=sys.argv[2]
for n,h in enumerate(sys.argv[3:],first):
 assert n<=40
 a=f'NBS_K{n:03}';r=subprocess.run([sys.executable,str(E/'NBS_kani.py'),a,'crates/aspis-r1-cost-probe',h,patch],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json';assert p.exists(),r.stdout+r.stderr
 x=json.loads(p.read_text());print(a,h,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status']!=0 or r.returncode!=0: print(r.stdout[-3500:]+r.stderr,flush=True);raise SystemExit(1)
