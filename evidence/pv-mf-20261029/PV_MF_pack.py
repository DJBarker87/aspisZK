#!/usr/bin/env python3
"""Compress generated tables deterministically; keep every file below 20 MB."""
import hashlib,json,lzma,re
from pathlib import Path
D=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
roots=['MODULES','EVIDENCE','HASH-CLAIMS','RECOUNT9','GAPS','PROTOCOL','FILES','COHORTS','BINDINGS','BINDING-MODULES','STALE','HASH-REVIEW','SUPPLEMENT','SOURCE-BINDINGS']
used=set()
def visit(name):
 if name in used:return
 used.add(name);j=json.loads((D/name).read_text())
 if isinstance(j,dict) and 'sharded' in j:
  for x in j['sharded']:visit(x['path'])
for n in roots:visit(n+'.json')
for p in D.glob('*-part*.json'):
 if p.name not in used:p.unlink()
# Leaf tables first so shard-index digests can be updated afterwards.
for name in sorted(used):
 p=D/name;b=p.read_bytes();j=json.loads(b)
 if isinstance(j,dict) and ('sharded' in j or 'compressed' in j):continue
 if len(b)>200_000:
  z=lzma.compress(b,preset=6);zn=name+'.xz';(D/zn).write_bytes(z)
  p.write_text(json.dumps({'compressed':{'path':zn,'sha256':sha(z),'bytes':len(z),'uncompressed_sha256':sha(b),'uncompressed_bytes':len(b)}},indent=1)+'\n')
for name in sorted(used):
 p=D/name;j=json.loads(p.read_text())
 if isinstance(j,dict) and 'sharded' in j:
  for r in j['sharded']:
   b=(D/r['path']).read_bytes();r.update(sha256=sha(b),bytes=len(b))
  p.write_text(json.dumps(j,indent=1)+'\n')
m=json.loads((D/'MANIFEST.json').read_text());m['parts']={}
for p in sorted(D.iterdir()):
 if p.is_file() and p.name not in ['MANIFEST.json','validation.json','release-gate-validation.json','negative-control.json','REPORT.md']:
  b=p.read_bytes();assert len(b)<20_000_000,p.name;m['parts'][p.name]={'sha256':sha(b),'bytes':len(b)}
(D/'MANIFEST.json').write_text(json.dumps(m,sort_keys=True,indent=1)+'\n')
