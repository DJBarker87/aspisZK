"""Losslessly retain selected-file inventories in bounded JSON shards/deltas."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013/evidence/s2j-20261023'
def encoded(x):return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
def sha(b):return hashlib.sha256(b).hexdigest()
def restore(p):
 x=json.loads((p/'objects-delta.json').read_text());base={}
 for part in x['base_parts']:
  raw=(E/part['file']).read_bytes();assert sha(raw)==part['sha256'];base.update(json.loads(raw))
 base.update(x['changed'])
 for k in x['removed']:base.pop(k)
 raw=encoded(base);assert sha(raw)==x['original_sha256'];return raw
if __name__=='__main__':
 candidates=sorted(E.glob('lean-*/objects.json'))
 if candidates:
  base=json.loads(candidates[-1].read_text());entries=sorted(base.items());parts=[]
  out=E/'object-base';out.mkdir(exist_ok=True)
  for i in range(0,len(entries),3000):
   p=out/f'part-{i//3000:03d}.json';raw=encoded(dict(entries[i:i+3000]));p.write_bytes(raw)
   parts.append(dict(file=str(p.relative_to(E)),sha256=sha(raw)))
  for p in candidates:
   values=json.loads(p.read_text());delta=dict(base_parts=parts,original_sha256=sha(p.read_bytes()),changed={k:v for k,v in values.items() if base.get(k)!=v},removed=[k for k in base if k not in values])
   (p.parent/'objects-delta.json').write_bytes(encoded(delta));assert restore(p.parent)==p.read_bytes();p.unlink()
