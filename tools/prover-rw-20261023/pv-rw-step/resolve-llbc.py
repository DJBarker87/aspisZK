"""Resolve shortened LLBC paths against immutable receipt pins, without changing receipts."""
from pathlib import Path
import json,subprocess,hashlib
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw-step-20261026'
rows=[]
for p in sorted(e.glob('pv-rw-step-*/receipt.json')):
 x=json.loads(p.read_text());artifacts=x.get('input_artifacts',{})
 for remote,a in artifacts.items():
  if not remote.endswith('.llbc'):continue
  dst=p.parent/'llbc-input.json'
  if not dst.exists():subprocess.run(['scp','dombarker@100.108.41.90:'+a['retained'],str(dst)],check=True)
  assert hashlib.sha256(dst.read_bytes()).hexdigest()==a['sha256']
  mappings=[]
  for name,b in a.get('source_bindings',{}).items():
   candidates=[full for full,digest in x['source_sha256'].items() if Path(full).name==Path(name).name and digest==b['llbc_source_sha256']]
   assert candidates,(p,name)
   mappings.append(dict(llbc_name=name,llbc_sha256=b['llbc_source_sha256'],pinned_source_paths=candidates,matches_immutable_pins=True))
  rows.append(dict(attempt=p.parent.name,llbc_sha256=a['sha256'],resolution=mappings,qualification='The original receipt conservatively reports false when Charon shortens paths to basenames. This independent resolution uses exact file-content hashes and the original immutable full-path input pins. No original whole-helper equivalence follows.'))
(e/'llbc-source-resolution.json').write_text(json.dumps(rows,indent=2)+'\n');print('resolved',len(rows),'LLBC inputs')
