"""Read-only final audit-input/object/source binding; no build or launcher work."""
from pathlib import Path
import json,hashlib,datetime
h=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/receipts7');x=json.loads((h/'20701-input.json').read_text())
def sha(p):
 d=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):d.update(b)
 return d.hexdigest()
rows=[]
for d in x['dependencies']:
 p=Path(d['resolved_object']);v=sha(p);rows.append(dict(module=d['module'],path=str(p),sha256=v,matches_audit_input=v==d['object_sha256'],bytes=p.stat().st_size))
src=Path(x['source_path']);assert sha(src)==x['source_sha256']
root=Path('/home/dombarker/project-offloads/aspis-joint-20261019/sources/R1Z')
full={p.name:dict(sha256=sha(p),bytes=p.stat().st_size) for p in root.glob('ProverRwFull*.lean')}
result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),target=x['module'],source_revision=x['source_revision'],source_sha256=x['source_sha256'],dependencies=rows,all_audit_input_objects_match=all(r['matches_audit_input'] for r in rows),raw_extracted_sources=full,qualification='Read-only hash binding after the final focused cached audit; not a coherent release replay, native world proof or release-artifact identity check.')
(h/'final-object-binding.json').write_text(json.dumps(result,indent=2)+'\n')
print(len(rows),'objects; all match',result['all_audit_input_objects_match']);assert result['all_audit_input_objects_match']
