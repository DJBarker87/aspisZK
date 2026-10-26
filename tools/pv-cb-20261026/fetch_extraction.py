"""Fetch a complete extraction and record the import-only adaptation."""
from pathlib import Path
import subprocess,json,hashlib,sys
n=sys.argv[1];root=Path(__file__).resolve().parents[2]
dst=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
base=f'dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-pv-cb-20261026/shipped-op{n}-generated/'
raw={}
for kind in ['Types','Funs']:
 p=dst/f'PV_CB_Op{n}{kind}.lean';assert not p.exists(),str(p)
 subprocess.run(['scp',base+kind+'.lean',str(p)],check=True)
 s=p.read_text();raw[kind]=hashlib.sha256(s.encode()).hexdigest()
 if kind=='Funs':
  assert 'FunsExternal' not in s,'Opaque external functions: cannot install source law'
  s=s.replace(f'import PVCBShippedOp{n}.Types',f'import R1Z.PV_CB_Op{n}Types');p.write_text(s)
r=dict(raw_sha256=raw,change='Only Funs import rewritten to own Types module; Types and emitted function bodies unchanged; no external function template.')
(root/f'evidence/pv-cb-20261026/op{n}-normalization.json').write_text(json.dumps(r,indent=2)+'\n')
