"""Serial lane-owned queue; abort on unresolved launch or lock/graph failure."""
from pathlib import Path
import subprocess,sys,json,os
E=Path(__file__).resolve().parent
jobs=json.loads(Path(sys.argv[1]).read_text())
for a,kind,target,cfg in jobs:
 env=dict(os.environ)
 if cfg:env['NDF_RUST_CFG']=cfg
 r=subprocess.run([sys.executable,str(E/'NDF_run.py'),a,kind,target],env=env)
 if r.returncode:raise SystemExit(r.returncode)
 if kind=='kani':
  g=json.loads((E/(a+'-graph-check.json')).read_text());l=json.loads((E/(a+'-lock-check.json')).read_text())
  assert g['graph_matches_frozen'] and l['unchanged']
