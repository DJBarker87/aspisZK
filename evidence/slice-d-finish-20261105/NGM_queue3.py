from pathlib import Path
import subprocess,json,sys,os
E=Path(__file__).resolve().parent
jobs=[]
for g in range(9):
 target='verifier::NGM_verifier::finish_control_'+(str(g)if g<8 else'rename')
 for invert in [False,True]:jobs.append((f'NGM_K{23+2*g+int(invert):03}',target,invert))
for a,target,invert in jobs:
 if (E/a/'receipt.json').exists():continue
 if (E/'NGM_HOLD').exists():raise SystemExit(0)
 env=dict(os.environ)
 if invert:env['NGM_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NGM_run.py'),a,'kani',target],capture_output=True,text=True,env=env)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Missing receipt: '+r.stdout[-1000:]+r.stderr[-1000:])
 x=json.loads(p.read_text());print(json.dumps({k:x[k]for k in ['attempt','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 if x['exit_status']!=int(invert):raise SystemExit(r.stdout[-2000:]+r.stderr[-1000:])
