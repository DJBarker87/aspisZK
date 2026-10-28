"""Read-only receipt recovery; never submit a compiler command."""
import subprocess,json,time
from pathlib import Path
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
cmd="""python3 - <<'INNER'
from pathlib import Path
import json
p=Path('/home/dombarker/project-offloads/codex-pv-fxmem-20261028/drop-counterexample-01')
print(json.dumps({n:(p/n).read_text() if (p/n).exists() else None for n in ['admission-before.json','reservation.log','admission-barrier.json','output.log','time.log']}))
INNER"""
for attempt in range(1,11):
 p=subprocess.run(['ssh','dombarker@100.108.41.90',cmd],text=True,capture_output=True)
 with (E/'transport.jsonl').open('a') as f:f.write(json.dumps(dict(operation='read-only native receipt recovery',attempt=attempt,exit=p.returncode,error=p.stderr,epoch=time.time()))+'\n')
 if p.returncode==0:
  j=json.loads(p.stdout)
  for n,s in j.items():
   if s is not None:(E/'drop-counterexample-01'/n).write_text(s)
  print(j['output.log']);break
 if p.returncode!=255:raise SystemExit(p.returncode)
 if attempt<10:time.sleep(60)
else:raise SystemExit('persistent transport failure after ten recovery attempts')
