from pathlib import Path
import shutil,hashlib,json
B=Path(__file__).resolve().parent
P=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIM_flat/NIM_exports_20261107');D=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104/NIX_seed_20261107/NIM_exports_20261107')
assert not D.exists();shutil.copytree(P,D)
rows=[dict(source=str(P/p.relative_to(D)),path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(D.rglob('*')) if p.is_file()]
(B/'NIX_NIM_SEED.json').write_text(json.dumps(dict(total_bytes=sum(r['bytes'] for r in rows),objects=rows),indent=2)+'\n')
p=B/'NIX_PATHS.json';paths=json.loads(p.read_text());paths.insert(1,str(D));p.write_text(json.dumps(paths,indent=2)+'\n');print('NIM retained object seed',sum(r['bytes'] for r in rows))
