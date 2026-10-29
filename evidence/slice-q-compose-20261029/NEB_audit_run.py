#!/usr/bin/env python3
"""Receipt for small Python-only audits; no Lean/Rust/Kani process."""
from pathlib import Path
import hashlib,json,subprocess,resource,sys,time
E=Path(__file__).resolve().parent;R=E.parent.parent
name=sys.argv[1];command=sys.argv[2:]
assert name.startswith('NEB_') and command[0]=='python3' and command[1].endswith(('_validate.py','_tests.py'))
start=time.monotonic()
with (E/(name+'_stdout.json')).open('w') as out,(E/(name+'_stderr.log')).open('w') as err:
 r=subprocess.run(command,cwd=R,stdout=out,stderr=err)
u=resource.getrusage(resource.RUSAGE_CHILDREN)
d=dict(target=command[1],command=command,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=bool(subprocess.check_output(['git','status','--porcelain'],cwd=R)),source_hashes={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in E.glob('NEB_*.py')},exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swaps=u.ru_nswap,print_axioms='not applicable: Python only',cgroup='not applicable: no prover/compiler',lean_attempts=0,kani_attempts=0)
(E/(name+'_receipt.json')).write_text(json.dumps(d,indent=1)+'\n');print(json.dumps({k:d[k] for k in ['target','exit_status','wall_seconds','peak_rss_bytes','swaps']}))
sys.exit(r.returncode)
