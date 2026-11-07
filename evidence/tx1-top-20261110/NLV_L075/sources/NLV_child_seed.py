from pathlib import Path
import hashlib,json,shutil
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-tx1-observed-20261110');rows=[]
for x in json.loads((B/'NLV_CHILD_SOURCE_PINS.json').read_text()):
 source=P/'NLR_generated'/(x['module']+'.lean')
 assert hashlib.sha256(source.read_bytes()).hexdigest()==x['sha256'],('Committed source mismatch',x['module'])
 q=B/'NLV_seed/NLR';q.mkdir(parents=True,exist_ok=True)
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=P/'NLR_objects'/(x['module']+suffix)
  if not p.exists():continue
  h=hashlib.sha256(p.read_bytes()).hexdigest();dst=q/p.name
  if not dst.exists():shutil.copy2(p,dst)
  assert hashlib.sha256(dst.read_bytes()).hexdigest()==h
  rows.append(dict(source=str(p),destination=str(dst),sha256=h,bytes=dst.stat().st_size,source_sha256=x['sha256'],source_revision=x['source_revision']))
 assert hashlib.sha256(source.read_bytes()).hexdigest()==x['sha256'],'Source changed during read-only import'
(B/'NLV_CHILD_OBJECT_PINS.json').write_text(json.dumps(rows,indent=2))
print('Copied two committed NLR interfaces read-only; no child root credit')
