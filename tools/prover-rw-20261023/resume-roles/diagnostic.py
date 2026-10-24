from pathlib import Path
import runpy,json,time,sys
D=Path(__file__).resolve().parent
start=time.monotonic();r=runpy.run_path(str(D/'reservation.py'))['admission'](requested=2*2**30)
r.update(command=['python3',str(D/'diagnostic.py')],wall_seconds=time.monotonic()-start,exit_status=0 if r['allowed'] else 78,compiler_invocations=0,scope='READONLY 2GiB admission diagnostic; no reservation or build',print_axioms='N/A')
p=D/'packet/readonly';p.mkdir(parents=True,exist_ok=False)
(p/'diagnostic.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k not in ['cgroups','uncapped_background','process_visibility','service_visibility','docker_visibility','meminfo']}))
sys.exit(r['exit_status'])
