"""Meter local Python evidence-only commands; never launch a prover."""
from pathlib import Path
import subprocess,time,resource,sys,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];name,target,*args=sys.argv[1:]
assert name.startswith('NFX_') and target in ['NFX_finalize.py','NFX_ledger.py','NFX_tests.py','NFX_artifacts.py']
start=time.monotonic();command=[sys.executable,str(E/target),*args]
with (E/(name+'.stdout')).open('w') as out,(E/(name+'.stderr')).open('w') as err:r=subprocess.run(command,cwd=R,stdout=out,stderr=err)
u=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt=dict(attempt=name,kind='python-evidence-check',target=[target,*args],command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swap='local Python ru_nswap='+str(u.ru_nswap)+'; no prover process',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in E.glob('NFX_*.py')},print_axioms='N/A Python; exact measured #print axioms/raw walks are checked inputs',lean_runs=0,kani_runs=0,extraction_runs=0)
(E/(name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n')
with (E/'NFX_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
print(json.dumps(receipt));sys.exit(r.returncode)
