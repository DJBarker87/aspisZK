"""Read-only source/object assessment in this job's isolated host workspace."""
from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
objects={p.name:{'sha256':sha(p),'bytes':p.stat().st_size} for p in B.glob('Port8EFF_*.olean')}
rows={}
for p in B.glob('lean-*/receipt.json'):
 x=json.loads(p.read_text())
 for name,entry in x.get('deps_fingerprint',{}).get('selected_objects',{}).items():
  obj=Path(entry['path'])
  if not str(obj).endswith('.olean'):continue
  source=obj.with_suffix('.lean');row={'object':entry,'source_present':source.is_file()}
  if source.is_file():row['host_source']={'path':str(source),'sha256':sha(source),'bytes':source.stat().st_size}
  rows[str(obj)]=row
out={'own_objects':objects,'selected_dependencies':rows,'qualification':'Read-only current host source assessment; historical cache source text is not proof of object identity. No coherent rebuild or ELF identity gate.'}
(B/'object-source-assessment.json').write_text(json.dumps(out,indent=2)+'\n')
