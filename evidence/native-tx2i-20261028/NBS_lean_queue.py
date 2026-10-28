from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for module in sys.argv[1:]:
 n=1+len(list(E.glob('NBS_L[0-9][0-9][0-9].json')));assert n<=100
 a=f'NBS_L{n:03}'
 r=subprocess.run(['python3',str(E/'NBS_build.py'),a,'lean/'+module+'.lean',module],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json';assert p.exists(),r.stdout+r.stderr
 x=json.loads(p.read_text());print(a,module,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status'] or r.returncode:
  print(r.stdout[-10000:]+r.stderr,flush=True);raise SystemExit(1)
