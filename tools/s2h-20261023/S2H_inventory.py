"""Lossless delta storage of large, mostly identical object inventories."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013/evidence/s2h-20261023'
def compact():
 basepath=E/'object-base.json'
 candidates=sorted(E.glob('lean-*/objects.json'))
 if not candidates:return
 if not basepath.exists():basepath.write_bytes(candidates[0].read_bytes())
 base=json.loads(basepath.read_text())
 for p in candidates:
  values=json.loads(p.read_text());delta={'base':'object-base.json','original_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'changed':{k:v for k,v in values.items() if base.get(k)!=v},'removed':[k for k in base if k not in values]}
  rebuilt=dict(base);rebuilt.update(delta['changed'])
  for k in delta['removed']:rebuilt.pop(k)
  assert hashlib.sha256((json.dumps(rebuilt,sort_keys=True,indent=2)+'\n').encode()).hexdigest()==delta['original_sha256']
  (p.parent/'objects-delta.json').write_text(json.dumps(delta,sort_keys=True,indent=2)+'\n');p.unlink()
if __name__=='__main__':compact()
