from pathlib import Path
import runpy,json,time,sys,subprocess
D=Path(__file__).resolve().parent
O=D/'packet/readonly';O.mkdir(parents=True,exist_ok=False)
t=time.monotonic()
r=runpy.run_path(str(D/'reservation.py'))['admission'](requested=2**30)
r.update(command=['python3',str(D/'diagnostic.py')],source_revision=(D/'revision.txt').read_text().strip(),wall_seconds=time.monotonic()-t,exit_status=0 if r['allowed'] else 78,compiler_invocations=0,scope='READONLY 1GiB diagnostic; no reservation/build',peak_rss='N/A diagnostic only',swap='N/A diagnostic only',print_axioms='N/A: no Lean')
(O/'diagnostic.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k not in ['cgroups','uncapped_background','process_visibility','service_visibility','docker_visibility','meminfo','uncapped_exclusive_usage']}))
sys.exit(r['exit_status'])
