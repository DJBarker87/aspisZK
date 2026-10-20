import json,sys
from pathlib import Path
h=Path(sys.argv[1]);p=json.loads((h/'plan-control.json').read_text());p.update(driver=str(h/'artifacts/pool_gate_trace'),out=str(h/'sweep/trace-control'),trace_dir=str(h/'traces/trace-control'))
for r in p['runs']:r['label']='trace-'+r['label']
(h/'plan-trace-control.json').write_text(json.dumps(p,indent=1))
