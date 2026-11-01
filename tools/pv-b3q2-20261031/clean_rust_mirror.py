"""Remove only unused duplicate formal sources from this job's Rust mirror.
Original sources and every compiled/imported proof source/object are retained.
"""
from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-b3q2-20261031');O=H/'direct-source';B=H.parent/'codex-pv-b3p6-20261028/source';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=json.loads((H/'env-J-private.json').read_text());assert all(str(O)not in p for p in env['LEAN_PATH'].split(':'))
manifest=json.loads((H/'frozen-manifest.json').read_text());before={str(p):sha(p)for p in (H/'lean').glob('*.lean')};before.update({str(p):sha(p)for p in (H/'lean-objects').glob('PV_B3Q_*')if p.is_file()})
rows=[]
for p in O.rglob('*.lean'):
 assert p.is_file()and not p.is_symlink()and p.resolve().is_relative_to(O.resolve()),str(p)
 original=B/p.relative_to(O);assert original.is_file()and sha(original)==sha(p),('not an unchanged duplicate',str(p))
 rows.append(dict(copy=str(p),original=str(original),sha256=sha(p),pv_b3p=p.name.startswith('PV_B3P_')))
for row in rows:Path(row['copy']).unlink()
assert all(Path(row['original']).is_file()and sha(Path(row['original']))==row['sha256']for row in rows)
assert all(Path(p).is_file()and sha(Path(p))==s for p,s in before.items())
x=dict(removed_duplicate_lean_sources=len(rows),pv_b3p_duplicates=sum(r['pv_b3p']for r in rows),rows=rows,originals_unchanged=True,proof_sources_and_objects_unchanged=True,rust_mirror_absent_from_lean_path=True,scope='Only this private Rust source mirror. No source content was edited and no source was compiled/imported from this location. Wallet/account/key files are not targets.')
(H/'rust-mirror-cleanup.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:v for k,v in x.items()if k!='rows'}))
