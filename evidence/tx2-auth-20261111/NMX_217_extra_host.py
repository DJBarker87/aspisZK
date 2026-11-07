from pathlib import Path
import json,hashlib
B=Path.cwd();x=json.loads((B/'NMX_217_KANI_EXTRA_INPUTS.json').read_text());assert x['source_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
for rel,item in x['files'].items():
 raw=item['text'].encode();assert hashlib.sha256(raw).hexdigest()==item['sha256']
 p=B/'NMX_src'/rel;p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==raw
 else:p.write_bytes(raw)
for parent,rel,target in x.get('path_edges',[]):assert (B/'NMX_src'/target).is_file(),(parent,rel,target)
print(json.dumps({'frozen_proof_only_inputs':{p:r['sha256'] for p,r in x['files'].items()}}))
