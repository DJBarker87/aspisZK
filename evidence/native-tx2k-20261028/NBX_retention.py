from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for i,op in enumerate([23,31,32,33,34,48,49,53],79):
 a=f'NBX_L{i:03}';n=f'NBX_InstalledOp{op}'
 r=subprocess.run(['python3',str(E/'NBX_build.py'),a,'lean/'+n+'.lean',n],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json';assert p.exists(),(a,r.stdout,r.stderr)
 rc=json.loads(p.read_text());print(a,op,rc['exit_status'],rc['wall_seconds'],flush=True)
 if rc['exit_status']!=0:raise SystemExit('STOP split single-field failure '+a)
