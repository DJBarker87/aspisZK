from pathlib import Path
import hashlib,shutil,json
B=Path.cwd();src=Path('/home/dombarker/project-offloads/codex-cx-decref-cache-20261028');dst=B/'NMX_NDB_seed';dst.mkdir(exist_ok=True);pins={}
for p in src.rglob('*'):
 if not p.is_file() or not p.relative_to(src).parts[0].startswith('NDB_'):continue
 if p.suffix not in ['.olean','.ir','.private','.server']:continue
 q=dst/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q);assert q.read_bytes()==p.read_bytes()
 pins[str(q.relative_to(B))]={'source':str(p),'sha256':hashlib.sha256(q.read_bytes()).hexdigest()}
assert (dst/'NDB_PrimaryWords.olean').is_file()
(B/'NMX_NDB_SEED.json').write_text(json.dumps(pins,indent=1)+'\n');print(json.dumps({'NDB_objects':len(pins)}))
