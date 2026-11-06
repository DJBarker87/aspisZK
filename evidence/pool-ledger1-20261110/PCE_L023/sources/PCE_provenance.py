from pathlib import Path
import json,hashlib,lzma,shutil
B=Path.cwd();C=Path('/home/dombarker/project-offloads/codex-pc-pool-ledger1-cache-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads(lzma.decompress((B/'PCE_IMPORTS.json.xz').read_bytes()));bad=[]
for rel,v in x.items():
 p=C/rel
 if not p.is_file() or sha(p)!=v['sha256']:bad.append(rel)
assert not bad,bad
pins={str(p):dict(sha256=sha(p),bytes=p.stat().st_size) for sub in ['PCE_generated','PCE_objects','PCE_native'] for p in (B/sub).rglob('*') if p.is_file()}
(B/'PCE_FINAL_PINS.json').write_text(json.dumps(dict(imports=len(x),all_imported_hashes_match=True,own_files=pins,disk=shutil.disk_usage(B)._asdict()),indent=1)+'\n')
print('PCE provenance PASS: all selected import hashes unchanged; own generated sources/objects/binaries pinned.')
