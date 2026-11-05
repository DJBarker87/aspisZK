from pathlib import Path
import subprocess,json,sys,os,re
E=Path(__file__).resolve().parent
jobs=[(88+2*g+int(inv),f'verifier::NGM_helpers::poly_g{g}',inv)for g in range(5)for inv in [False,True]]
jobs += [(98,'verifier::NGM_helpers::round_g0',False),(99,'verifier::NGM_helpers::round_g0',True),(100,'verifier::NGM_helpers::poly_g5',False)]
for number,target,invert in jobs:
 a=f'NGM_K{number:03}';env=dict(os.environ)
 if invert:env['NGM_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NGM_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr);p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Missing receipt: '+r.stdout[-1000:]+r.stderr[-1000:])
 x=json.loads(p.read_text());raw=(E/a/'stdout.log').read_text();print(json.dumps({k:x[k]for k in ['attempt','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 verdict='VERIFICATION:- FAILED'if invert else'VERIFICATION:- SUCCESSFUL'
 if x['exit_status']!=int(invert)or verdict not in raw or re.search(r'TIMEOUT|timed out|memory limit exceeded|SIGKILL',raw,re.I):raise SystemExit('Excluded/unexpected verdict: '+raw[-1500:])
