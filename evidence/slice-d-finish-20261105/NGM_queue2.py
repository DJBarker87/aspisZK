from pathlib import Path
import subprocess,json,sys,os
E=Path(__file__).resolve().parent
jobs=[('NGM_E001','extract','NGM_FinishRef',False),('NGM_K006','kani','verifier::NGM_verifier::finish_control_0',True)]
for g in range(1,8):
 for invert in [False,True]:jobs.append((f'NGM_K{7+2*(g-1)+int(invert):03}','kani',f'verifier::NGM_verifier::finish_control_{g}',invert))
for invert in [False,True]:jobs.append((f'NGM_K{21+int(invert):03}','kani','verifier::NGM_verifier::finish_control_rename',invert))
for a,kind,target,invert in jobs:
 if (E/a/'receipt.json').exists():continue
 env=dict(os.environ)
 if invert:env['NGM_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NGM_run.py'),a,kind,target],capture_output=True,text=True,env=env)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Missing receipt: '+r.stdout[-2000:]+r.stderr[-1000:])
 x=json.loads(p.read_text());print(json.dumps({k:x[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 if x['exit_status']!=int(invert):raise SystemExit(r.stdout[-2500:]+r.stderr[-1000:])
