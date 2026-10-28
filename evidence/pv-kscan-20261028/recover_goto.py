"""Copy existing metadata only; read original goto binaries, never rebuild."""
from pathlib import Path
import json,hashlib
R=Path('/home/dombarker/project-offloads/codex-pv-kscan-20261028');out=R/'R01';target=out/'target';target.mkdir(parents=True,exist_ok=True)
allowed=set(json.loads((R/'pass-harnesses.json').read_text()));inventory=[]
for root in R.parent.glob('codex-pv-*'):
 if root==R:continue
 for p in root.rglob('*.kani-metadata.json'):
  try:j=json.loads(p.read_text())
  except (OSError,ValueError):continue
  hs=[]
  for h in j.get('proof_harnesses',[]):
   if h['pretty_name'] not in allowed:continue
   f=Path(h['goto_file']);f=f.with_name(f.name.replace('.symtab.out','.out'))
   if f.exists():hs.append(h)
  if hs:
   j['proof_harnesses']=hs;q=target/(hashlib.sha256(str(p).encode()).hexdigest()+'.kani-metadata.json');q.write_text(json.dumps(j))
   inventory.append(dict(metadata=str(p),metadata_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),copied=str(q),harnesses=[h['pretty_name'] for h in hs]))
(out/'recovered-metadata.json').write_text(json.dumps(inventory,indent=2)+'\n');print('existing metadata',len(inventory),'harness entries',sum(len(x['harnesses']) for x in inventory),flush=True)
