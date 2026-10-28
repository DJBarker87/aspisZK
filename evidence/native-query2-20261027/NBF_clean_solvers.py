from NBF_host import *
import sys
label=sys.argv[1]
r=py(f'''from pathlib import Path
import json,hashlib
root=Path({(B+'/NBF_tmp')!r});found=[]
for p in root.rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat') and p.suffix=='.cnf' or p.name.startswith('smt2_dec_problem')):
  found.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()));p.unlink()
print(json.dumps(dict(label={label!r},removed=found,remaining_files=[str(p) for p in root.rglob('*') if p.is_file()])))
''')
assert r.returncode==0,r.stderr
(E/('NBF_SOLVER_CLEAN_'+label+'.json')).write_text(r.stdout)
print(r.stdout)
