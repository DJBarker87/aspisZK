from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for n,mode in [(62,'byte-negative'),(63,'error-negative'),(64,'place-negative'),(65,'allocation-negative')]:
 a=f'NFV_K{n:03}'
 subprocess.run([sys.executable,str(E/'NFV_helper_log.py'),mode],check=True)
 r=subprocess.run([sys.executable,str(E/'NFV_kani_run.py'),a,'pair_forest::NFV_Helper::association'],capture_output=True,text=True)
 p=E/a/'receipt.json'
 if not p.exists():print(r.stdout+r.stderr);raise SystemExit('STOP missing terminal receipt')
 text=(E/a/'stdout.log').read_text();rc=json.loads(p.read_text())
 row=dict(attempt=a,mode=mode,exit=rc['exit_status'],timeout='timed out' in text.lower(),unwind='unwinding assertion' in text)
 with (E/'NFV_HELPER_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
 if rc['exit_status'] not in [0,1,124]:raise SystemExit('STOP unexpected exit')
