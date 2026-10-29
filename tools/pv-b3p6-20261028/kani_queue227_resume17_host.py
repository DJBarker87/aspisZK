"""Thirty budgeted new splits, only after direct refusals and std-parity work."""
from pathlib import Path
from run import H
import json,time,subprocess,shutil
R=H/'resume17'
assert (R/'STD-PARITY.json').exists()
while not any(H.glob('lean-73804*/receipt/receipt.json')):time.sleep(15)
for q in json.loads((R/'KANI-QUEUE.json').read_text()):
 ident=q['id']
 if any(R.glob(f'K{ident}*/receipt/receipt.json')):continue
 while (R/'lean-work-pending.json').exists():time.sleep(15)
 ident=q['id'];cmd=['python3','kani227_resume17_host.py',str(ident),q['harness'],'leaf']
 for retry in range(11):
  p=H/'admission-not-before.json'
  while p.exists()and(left:=json.loads(p.read_text())['epoch']-time.time())>0:time.sleep(min(30,left))
  with (R/f'kani-queue-{ident}-{retry}.log').open('w')as f:s=subprocess.run(cmd,cwd=H,stdout=f,stderr=subprocess.STDOUT).returncode
  print(json.dumps(dict(id=ident,harness=q['harness'],exit=s,retry=retry)),flush=True)
  if s!=78:break
 else:raise SystemExit('admission retries exhausted')
 # These are only this run's proof-tool temporaries; no Rust/Lean sources,
 # receipts, keys, or other job's files can be in this private generated dir.
 d=R/(f'K{ident}-tmp')
 if d.exists():
  entries=[dict(path=str(p),bytes=p.stat().st_size)for p in d.rglob('*')if p.is_file()]
  (R/f'K{ident}-solver-cleanup.json').write_text(json.dumps(dict(scope_inactive=True,only_private_solver_temporary_directory=str(d),removed=entries),indent=2)+'\n')
  shutil.rmtree(d)
 if not any(R.glob(f'K{ident}*/receipt/receipt.json')):raise SystemExit('own input/prelaunch failure; correct before queue continues')
