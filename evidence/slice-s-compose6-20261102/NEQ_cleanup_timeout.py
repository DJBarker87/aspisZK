from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-slice-s-compose6-20261029');r=b/'NEQ_tmp';out=[]
for p in r.rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem')):
  out.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()));p.unlink()
print(json.dumps(dict(attempt='NEQ_K081',reason='90s timeout; no credit; unchanged shape never resubmitted',deleted_solver_temps=out)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr;(E/'NEQ_K081_TEMP_CLEANUP.json').write_text(r.stdout)
