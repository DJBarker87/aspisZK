from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[(3,'shape_contract',True),(4,'shape_weak_contract',False),(5,'shape_real',False),(6,'shape_unimplied',False),(7,'shape_frame',False),(8,'copy_positive',False),(9,'copy_negative',False)]
for k,h,inv in jobs:
 a=f'NGH_K{k:03}';env=dict(os.environ,NGH_CORE='1')
 if inv:env['NGH_INVERT']='1'
 r=subprocess.run(['python3',str(E/'NGH_run.py'),a,'kani','field::NGH_contracts::'+h],env=env,capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise RuntimeError(r.stdout+r.stderr)
 x=json.loads(p.read_text());print(a,h,x['exit_status'],x['wall_seconds'],flush=True)
