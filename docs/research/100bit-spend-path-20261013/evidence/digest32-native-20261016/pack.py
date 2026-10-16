#!/usr/bin/env python3
"""Package retained native receipts only; no execution or key material."""
from pathlib import Path
import hashlib,io,json,tarfile
here=Path(__file__).resolve().parent;root=here.parents[4];src=root/'.j1-digest32-native'
sha=lambda b:hashlib.sha256(b).hexdigest();data={}
for p in sorted(src.rglob('*')):
 if p.is_file() and 'unused-focused-kit' not in p.parts:data[str(p.relative_to(src))]=p.read_bytes()
data['pack.py']=Path(__file__).read_bytes()
data['SHA256SUMS']=(''.join(sha(b)+'  '+n+'\n' for n,b in sorted(data.items()))).encode()
p=here/'evidence.tar.gz'
with tarfile.open(p,'w:gz') as t:
 for n,b in sorted(data.items()):
  x=tarfile.TarInfo(n);x.mode=0o644;x.size=len(b);t.addfile(x,io.BytesIO(b))
m={'archive':p.name,'archive_sha256':sha(p.read_bytes()),'archive_bytes':p.stat().st_size,'entries':len(data),'summary':json.loads(data['SUMMARY.json']),'scope':'Native finite gates only; no SBF/CU, no formal theorem.'}
(here/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print(m['archive_sha256'],m['archive_bytes'],m['entries'])
