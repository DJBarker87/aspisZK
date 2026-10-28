"""Serial lane-owned batch; inspect every terminal receipt before the next launch."""
from pathlib import Path
import subprocess,json,sys,os
E=Path(__file__).resolve().parent
for a,target,expect,extra in json.loads(Path(sys.argv[1]).read_text()):
 env=dict(os.environ,**extra)
 r=subprocess.run([sys.executable,str(E/'NDD_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
 p=E/a/'receipt.json'
 if not p.exists():print(r.stdout+r.stderr);raise SystemExit('no terminal receipt; recover, do not resubmit')
 rc=json.loads(p.read_text());log=(E/a/'stdout.log').read_text()
 print(json.dumps(dict(attempt=a,target=target,exit=rc['exit_status'],wall=rc['wall_seconds'],expected=expect)),flush=True)
 if 'timed out' in log.lower() or rc['exit_status'] in [124,137]:raise SystemExit('timed-out/killed shape; split it, advance independent work')
 if expect=='PASS' and not ('VERIFICATION:- SUCCESSFUL' in log and rc['exit_status']==0):raise SystemExit('unexpected positive outcome')
 if expect=='FAIL' and not ('VERIFICATION:- FAILED' in log and 'Failed Checks:' in log):raise SystemExit('negative control did not fail as required')
