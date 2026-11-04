#!/usr/bin/env python3
"""Meter a Python-only ledger status/test command; no build or prover interface."""
import datetime,hashlib,json,resource,subprocess,sys,time
from pathlib import Path
E=Path(__file__).resolve().parent;R=E.parent.parent
name,target,*args=sys.argv[1:]
assert name.startswith('NFK_') and target in {'NFK_validate.py','NFK_tests.py'}
command=[sys.executable,str(E/target),*args];start=time.monotonic()
source_hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in E.glob('NFK_*.py')}
with (E/(name+'.stdout')).open('w') as out,(E/(name+'.stderr')).open('w') as err:
 result=subprocess.run(command,cwd=R,stdout=out,stderr=err)
r=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt=dict(source_sha256=source_hashes,attempt=name,command=command,target=[target,*args],exit_status=result.returncode,wall_seconds=time.monotonic()-start,peak_child_rss_bytes=r.ru_maxrss if sys.platform=='darwin' else r.ru_maxrss*1024,swap='unmeasured Python status checks; no prover process',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),print_axioms='N/A: Python; exact historical axiom outputs validated in NFK inputs',lean_runs=0,kani_runs=0)
(E/(name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n')
with (E/'NFK_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(receipt,sort_keys=True)+'\n')
print(json.dumps(receipt));sys.exit(result.returncode)
