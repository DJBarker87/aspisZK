"""Match reused cohort objects to surviving successful compilation receipts and inputs."""
from pathlib import Path
import hashlib,json
B=Path(__file__).resolve().parent
manifest={r['module']:r for r in map(json.loads,(B/'NER_MANIFEST.jsonl').read_text().splitlines())}
rows={r['module']:r for r in map(json.loads,(B/'NER_SOURCE_RESOLVED.jsonl').read_text().splitlines())}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
roots=[Path('/home/dombarker/project-offloads/'+s) for s in ['codex-cx-replay-dry-20261026','codex-cx-sound-int2-20261025','codex-cx-reconcile-cache-20261028']]
matched=[];unreadable=[]
for root in roots:
 for receipt in sorted(root.glob('*/receipt.json')):
  try:c=json.loads(receipt.read_text())
  except json.JSONDecodeError:
   unreadable.append(str(receipt));continue
  m=c.get('module');cmd=c.get('command',[])
  if not isinstance(m,str) or m not in rows or c.get('exit_status')!=0 or '-o' not in cmd:continue
  obj=Path(cmd[cmd.index('-o')+1]);obj=obj if obj.is_absolute() else root/obj
  if not obj.exists() or sha(obj)!=manifest[m]['artifacts'][0]['sha256']:continue
  sources=c.get('source_hashes',{})
  if len(sources)!=1:continue
  src,digest=next(iter(sources.items()));snap=receipt.parent/'sources'/src
  if not snap.exists():continue
  assert sha(snap)==digest
  rows[m].update(source_sha256=digest,source_path=str(snap),source_basis='successful receipt source and matching surviving cohort object',source_receipt=str(receipt),source_revision=c.get('source_revision'))
  rows[m].pop('candidates',None);rows[m].pop('candidate_sha256',None);matched.append(m)
(B/'NER_SOURCE_RECEIPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows.values()))
print(json.dumps({'unreadable_receipts':unreadable,'receipt_matches':len(set(matched)),'unresolved':[r['module'] for r in rows.values() if not r['source_sha256']]}))
