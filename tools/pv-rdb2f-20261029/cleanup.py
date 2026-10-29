"""Hash then remove only this task's rebuildable outputs; never touch source or keys."""
from pathlib import Path
import hashlib,json,lzma,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2f-20261029');assert D.name=='codex-pv-rdb2f-20261029'
raw=lzma.decompress((D/'closure-fingerprint.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(D/'closure-fingerprint.json.sha256').read_text().strip();j=json.loads(raw)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for r in j['objects']:assert sha(Path(r['path']))==r['object_sha256'],r['module']
binary=Path(j['binary']['path']);assert sha(binary)==j['binary']['sha256']
rows=[]
for name in ['target','lean-objects']:
 p=D/name;assert p.is_dir()and not p.is_symlink();files=[q for q in p.rglob('*')if q.is_file()and not q.is_symlink()];rows.append(dict(path=str(p),files=len(files),bytes=sum(q.stat().st_size for q in files)));shutil.rmtree(p)
(D/'cleanup.json').write_text(json.dumps(dict(removed=rows,verified_objects=len(j['objects']),binary=j['binary'],retained=['all sources','source/feature/object manifests','raw receipts','axioms outputs','source snapshots'],keys_touched=False,other_job_writes=False),indent=2)+'\n');print(json.dumps(rows))
