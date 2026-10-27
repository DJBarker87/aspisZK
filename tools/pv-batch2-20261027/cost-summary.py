"""Summarize inclusive, finite function costs; no whole-prover attribution."""
from pathlib import Path
import json,hashlib,sys
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027');label=sys.argv[1];P=H/'candidate'/label/'receipt/stdout.log';rows=[]
for line in P.read_text().splitlines():
 name,n,seconds=line.split();rows.append(dict(name=name,iterations=int(n),wall_seconds=float(seconds),microseconds_per_call=float(seconds)*1e6/int(n)))
r=dict(scope='Finite native inclusive microbenchmark on one fixed input; allocation included for original new and both materialize owners; not a source proof, worst-case bound, or attribution of whole-prover regression',rows=rows,probe_sha256=hashlib.sha256((H/'function-cost/function-cost.rs').read_bytes()).hexdigest())
(H/'function-cost-summary.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
