from pathlib import Path
import json,shutil,hashlib
B=Path(__file__).resolve().parent
paths=json.loads((B/'NKA_PREDECESSOR_PATHS.json').read_text())
orig=Path(paths[0]);dest=B/'NKA_NJT_seed';assert not dest.exists();shutil.copytree(orig,dest)
ledger=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NJW_20261108/NJW_exports_20261108');ld=B/'NKA_NJW_seed';assert not ld.exists();shutil.copytree(ledger,ld)
pins=[]
for source,target in [(orig,dest),(ledger,ld)]:
 for p in sorted(target.rglob('*')):
  if p.is_file():pins.append(dict(source=str(source/p.relative_to(target)),path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
paths=[str(dest) if p==str(orig) else p for p in paths];paths.insert(1,str(ld));paths.insert(0,str(B/'NKA_objects'))
(B/'NKA_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n')
(B/'NKA_SEED.json').write_text(json.dumps(dict(files=pins,total_bytes=sum(p['bytes'] for p in pins),cargo_target_dir=str(B/'NKA_target')),indent=2)+'\n')
print('NKA predecessor exports copied and hashed')
