#!/usr/bin/env python3
"""Inventory exact focused warm imports for dependent caller checks."""
from pathlib import Path
import hashlib,json,os,struct,sys
R=Path(__file__).resolve().parents[2]
# Reuse the existing olean-header reader, without its command-line driver.
code=(R/'tools/s126-sdk-20261021/pin-imports.py').read_text().split('\nB=Path',1)[0]
ns={};exec(compile(code,'pin-imports.py/header-reader','exec'),ns);imports=ns['imports']
roots=[Path('/tmp/s126-current-caller-20261021-objects')]+[Path(x) for x in Path('/tmp/s126-round-trace-path-20261024.txt').read_text().strip().split(':')]
names=['S1OwnedStage1FinishChildrenV1','S1TopPrepareY1ProvenanceV1','S1AcceptedSemanticNumericV1']
seen={};todo=names[:]
while todo:
 n=todo.pop()
 if n in seen:continue
 rel=Path(*n.split('.')).with_suffix('.olean');p=next((d/rel for d in roots if (d/rel).is_file()),None)
 assert p is not None,n
 files=[]
 for suffix in ['.olean','.olean.server','.olean.private','.ir']:
  q=p.with_suffix(suffix)
  if q.is_file():files.append(dict(path=str(q.resolve()),relative=str(rel.with_suffix(suffix)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
 seen[n]=dict(name=n,files=files,imports=imports(p));todo+=seen[n]['imports']
out=Path('/tmp/s126-numeric-caller-imports-20261024.json');out.write_text(json.dumps(dict(modules=list(seen.values())),separators=(',',':'))+'\n')
print(json.dumps(dict(modules=len(seen),files=sum(len(v['files']) for v in seen.values()),bytes=sum(f['bytes'] for v in seen.values() for f in v['files']),inventory=str(out))))
