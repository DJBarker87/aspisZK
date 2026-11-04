from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[('NGH_L014','lean','NGH_WideBridge'),('NGH_L015','lean','NGH_COMBINED_IMPORT'),('NGH_L016','lean','NGH_Driver'),('NGH_L017','review','NGH_Driver')]
for a,kind,h in jobs:
 if a=='NGH_L015':subprocess.run(['python3',str(E/'NGH_make_audit.py')],check=True)
 r=subprocess.run(['python3',str(E/'NGH_run.py'),a,kind,h],env=dict(os.environ,NGH_REVIEW_OUTPUT='NGH_review_wide'),capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr);p=E/a/'receipt.json'
 if not p.exists():raise RuntimeError(r.stdout+r.stderr)
 x=json.loads(p.read_text());print(a,h,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status']!=0:raise RuntimeError(r.stdout[-4000:]+r.stderr)
