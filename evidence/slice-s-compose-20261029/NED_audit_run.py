"""Measure a Python-only lane audit; never launches a proof/compiler job."""
from pathlib import Path
import subprocess,json,hashlib,time,resource,sys
E=Path(__file__).resolve().parent;R=E.parent.parent
name,script=sys.argv[1:];assert script in ['NED_validate.py','NED_tests.py','NED_check_contract_patch.py','NED_validate_native_windows.py','NED_validate_bindings.py','NED_check_bindings_patch.py','NED_verify_final.py']
start=time.monotonic();cmd=['python3',str(E/script)]
with (E/(name+'.stdout.log')).open('w') as out,(E/(name+'.stderr.log')).open('w') as err:r=subprocess.run(cmd,stdout=out,stderr=err,cwd=R)
u=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt=dict(target=script,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swaps=u.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=bool(subprocess.check_output(['git','status','--porcelain'])),source_sha256=hashlib.sha256((E/script).read_bytes()).hexdigest(),print_axioms='N/A: Python-only evidence/schema audit',cgroup='N/A: no Rust/Kani/Lean execution')
(E/(name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(receipt));sys.exit(r.returncode)
