from pathlib import Path
import subprocess,json,sys,os
E=Path(__file__).resolve().parent
jobs=[('NGM_K003','kani','weights::NGM_weights::copy_control',False),('NGM_K004','kani','weights::NGM_weights::copy_control',True)]
jobs += [(f'NGM_L{i:03}','lean',n,False) for i,n in enumerate(['NGM_NGC_FinishFrame','NGM_QueryExit','NGM_QEquality','NGM_GuardExact','NGM_GuardRef/Types','NGM_GuardRef/Funs','NGM_GuardRawModel'],4)]
for a,kind,target,invert in jobs:
 env=dict(os.environ)
 if invert:env['NGM_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NGM_run.py'),a,kind,target],capture_output=True,text=True,env=env)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Missing receipt: '+r.stdout+r.stderr)
 x=json.loads(p.read_text());print(json.dumps({k:x[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 if x['exit_status']!=int(invert):raise SystemExit(r.stdout[-2000:]+r.stderr[-1000:])
