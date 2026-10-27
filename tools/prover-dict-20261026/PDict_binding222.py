"""Read-only post-audit object/source binding; does not launch any build."""
from pathlib import Path
import hashlib,json,sys
job=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026')
j=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
x=json.loads((job/'receipts222/22299-input.json').read_text());rows=[]
for d in x['dependencies']:
 p=Path(d['resolved_object']);now=sha(p)
 rows.append(dict(module=d['module'],expected=d['object_sha256'],actual=now,match=now==d['object_sha256'],size=p.stat().st_size))
owned=[]
for d in json.loads((job/'accepted-source-binding222.json').read_text()):
 p=j/'sources'/(d['module']+'.lean');now=sha(p)
 owned.append(dict(module=d['module'],input_sha256=d['source_sha256'],current_sha256=now,match=now==d['source_sha256']))
raw=[]
for n in ['ProverRwFullFuns','ProverRwFullTypes','ProverRwFullExternalTypes','ProverRwFullExternalFuns']:
 p=j/'sources/R1Z'/(n+'.lean');raw.append(dict(module='R1Z/'+n,source_sha256=sha(p),size=p.stat().st_size))
y=dict(audit_attempt=22299,input_source_revision=x['source_revision'],audit_source_sha256=x['source_sha256'],deps_fingerprint=x['deps_fingerprint'],dependency_objects=rows,owned_sources=owned,raw_sources=raw,all_objects_match=all(r['match'] for r in rows),all_owned_sources_match=all(r['match'] for r in owned),qualification='Read-only hash comparison against focused audit inputs; not a coherent frozen release rebuild.')
(job/'binding222-final.json').write_text(json.dumps(y,indent=2)+'\n');print('dependency objects',len(rows),'owned sources',len(owned),'all match',y['all_objects_match'],y['all_owned_sources_match'])
