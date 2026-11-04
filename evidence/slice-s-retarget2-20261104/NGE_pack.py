"""Store immutable large inputs once; retain verified references per receipt."""
from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent;packed=[]
for name in ['NGE_EXPECTED_IMPORTS.jsonl','NGE_AUDIT_ROOTS.json']:
 canonical=E/name;data=canonical.read_bytes();h=hashlib.sha256(data).hexdigest()
 for p in sorted(E.glob('NGE_L*/sources/'+name)):
  assert p.read_bytes()==data,('snapshot differs',p)
  reference=dict(path=name,sha256=h,bytes=len(data),original_snapshot=str(p.relative_to(E)))
  p.with_name(p.name+'.ref.json').write_text(json.dumps(reference,indent=1)+'\n');p.unlink();packed.append(reference)
# Compress any unexpectedly large log exactly as rule 12 requires.
for p in E.rglob('*'):
 if p.is_file() and p.stat().st_size>20_000_000:
  assert not p.name.endswith('.xz'),('oversized compressed file',p)
  data=p.read_bytes();Path(str(p)+'.sha256').write_text(hashlib.sha256(data).hexdigest()+'\n');Path(str(p)+'.xz').write_bytes(lzma.compress(data,preset=6));p.unlink()
for p in E.glob('NGE_L*/sources/*.ref.json'):
 x=json.loads(p.read_text());raw=(E/x['path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==x['sha256'] and len(raw)==x['bytes']
packed=[json.loads(p.read_text()) for p in sorted(E.glob('NGE_L*/sources/*.ref.json'))]
(E/'NGE_PACK.json').write_text(json.dumps(dict(status='PASS',packed=packed,principle='Input bytes retained once with per-receipt hashes; no source/proof/receipt removed'),indent=1)+'\n')
print(json.dumps(dict(references=len(packed))))
