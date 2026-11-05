"""Serial owned queue; no scope overlaps and no automatic failure reruns."""
from pathlib import Path
import subprocess,json,sys,hashlib
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);jobs=json.loads(Path(sys.argv[2]).read_text())
for k,job in enumerate(jobs,start):
 a=f'NIO_K{k:03d}';client=E/(a+'-client.log')
 prepared=subprocess.run([sys.executable,str(E/job.get('script','NIO_native_prepare.py')),*map(str,job['prepare'])],capture_output=True,text=True)
 if prepared.returncode:
  (E/(a+'-prepare-error.log')).write_text(prepared.stdout+prepared.stderr);raise SystemExit('Own preparation failed: '+a)
 with client.open('w') as f:r=subprocess.run([sys.executable,str(E/'NIO_kani_run.py'),a,job['harness']],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Missing terminal receipt: '+a+'; inspect client log')
 d=json.loads(p.read_text());s=(E/a/'stdout.log').read_text()
 verdict='TIMEOUT' if 'timed out' in s else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in s else 'FAIL' if 'VERIFICATION:- FAILED' in s else 'REJECT'
 row=dict(attempt=a,job=job,verdict=verdict,exit=d['exit_status'],source_sha256=hashlib.sha256((E/(a+'-NIO_native.patch')).read_bytes()).hexdigest())
 with (E/'NIO_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(a+' '+verdict,flush=True)
 if verdict!=job['expected']:raise SystemExit('Unexpected verdict; isolate '+a+' before continuing')
