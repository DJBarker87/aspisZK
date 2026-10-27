"""Hash then remove only this job's completed Lean object cache."""
from pathlib import Path
import hashlib,json,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-3-20261027');p=B/'LPc_objects'
assert p.parent==B and not p.is_symlink()
rows={str(f.relative_to(B)):{'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size} for f in p.rglob('*') if f.is_file()}
(B/'LPc_LeanObjectHashes.json').write_text(json.dumps(rows,indent=2)+'\n')
size=sum(v['bytes'] for v in rows.values());shutil.rmtree(p)
r={'removed':str(p),'files':len(rows),'bytes':size,'keys_generated_or_deleted':False,'shared_coherent_objects':'untouched','source_and_receipt_trees':'retained','dependency_verification':'completed before removal in LPc_final-dependency-hashes.json'}
(B/'LPc_LeanCleanup.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
