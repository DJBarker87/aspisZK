"""Inventory compiled scratch and remove only key-free rebuildable caches.
Keep source, IR, receipts, binaries/keys in artifact dirs, and all ledgers.
Never follows or removes the targets of private object links.
"""
from pathlib import Path
import hashlib,json,shutil,time
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
objects={}
D=H/'lean-objects'
for p in D.rglob('PV_B2_*.olean'):
 if p.is_file():objects[str(p.relative_to(D))]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,symlink=p.is_symlink())
(H/'OUTPUT-OBJECT-PINS.json').write_text(json.dumps(objects,indent=2)+'\n')
rows=[]
for name in ['charon-target','lean-objects']:
 d=H/name;assert d.parent==H and not d.is_symlink()
 suspected=[str(p.relative_to(H)) for p in d.rglob('*') if p.is_file() and any(s in p.name.lower() for s in ['keypair','secret-key','wallet-key'])]
 count=sum(1 for p in d.rglob('*') if p.is_file())
 if suspected:action='retained entire cache: suspected key paths; no key cleanup authorized'
 else:shutil.rmtree(d);action='removed key-free compiled scratch'
 rows.append(dict(path=str(d),files_including_private_object_links=count,suspected_key_paths=suspected,action=action))
r=dict(utc=time.time(),paths=rows,object_manifest='OUTPUT-OBJECT-PINS.json',keys='all original task/SBF keys, source, fixtures and nonce ledgers retained; no key file removed or moved',shared_caches='untouched',print_axioms='N/A: file hygiene, no build')
(H/'CACHE-CLEANUP.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
