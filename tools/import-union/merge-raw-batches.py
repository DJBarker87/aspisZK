#!/usr/bin/env python3
"""Merge successful bounded comparison outputs into the complete raw census."""
import hashlib,json
from pathlib import Path
W=Path(__file__).resolve().parent
E=W/'evidence'
manifest=json.loads((E/'raw-batch-manifest.json').read_text())
p=E/'raw-union.jsonl';enumeration=p.read_bytes()
assert hashlib.sha256(enumeration).hexdigest()==manifest['enumeration_sha256']
records=[json.loads(l) for l in (E/'modules.jsonl').read_text().splitlines()]
latest={r['module']:r for r in records}
parts=[enumeration];found={};types={}
for batch in manifest['batches']:
 r=latest[batch['module']]
 assert r['exit']==0 and r['source_sha256']==batch['source']['sha256'] and r.get('rebuild_epoch')==batch['source']['rebuild_epoch'],r
 content=(W/batch['output']).read_bytes()
 local=[]
 for l in content.decode().splitlines():
  k,v=l.split(' ',1);v=json.loads(v)
  if k=='RAW_DUP':
   assert v[0] not in found and v[1]==manifest['candidates'][v[0]],v
   found[v[0]]=v;local.append(v[0])
  elif k=='RAW_DUP_TYPE':types.setdefault(v[0],[]).append(v[1])
  else:raise RuntimeError(k)
 assert sorted(local)==sorted(batch['names']),batch['module']
 parts.append(content)
assert found.keys()==manifest['candidates'].keys()
for n,os in manifest['candidates'].items():assert sorted(types[n])==sorted(o for o,_ in os),n
(E/'raw-union-enumeration.jsonl').write_bytes(enumeration)
p.write_bytes(b''.join(parts))
(E/'raw-census-merge.json').write_text(json.dumps({'modules':manifest['modules'],'declarations':manifest['declarations'],'duplicate_names':len(found),'batches':len(manifest['batches']),'all_types_compared_as_expressions':True,'enumeration_sha256':manifest['enumeration_sha256'],'combined_sha256':hashlib.sha256(p.read_bytes()).hexdigest()},indent=2)+'\n')
print('merged complete raw census:',manifest['modules'],'modules',len(found),'duplicate type checks')
