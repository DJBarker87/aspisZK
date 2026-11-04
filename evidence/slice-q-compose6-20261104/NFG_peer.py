"""Read immutable peer inputs, preserving Git blob identity and archive hash."""
from pathlib import Path
import base64,hashlib,json,lzma
E=Path(__file__).resolve().parent
def load():
 raw=lzma.decompress((E/'NFG_NFF_INPUTS.json.xz').read_bytes())
 assert hashlib.sha256(raw).hexdigest()==(E/'NFG_NFF_INPUTS.json.sha256').read_text().strip()
 d=json.loads(raw);blobs={}
 for oid,encoded in d['blobs'].items():
  b=base64.b64decode(encoded,validate=True)
  assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==oid,('peer Git blob drift',oid)
  blobs[oid]=b
 return {name:blobs[oid] for name,oid in d['paths'].items()}
if __name__=='__main__':
 d=load();attempts=[json.loads(l) for l in d['NFF_ATTEMPTS.jsonl'].decode().splitlines()]
 for r in attempts:
  if r['attempt'].startswith('NFF_K'): print(r['attempt'],r.get('target'),r['exit_status'])
