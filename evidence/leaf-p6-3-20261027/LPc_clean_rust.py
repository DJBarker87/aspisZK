"""Hash then remove this job's completed Rust/Kani target cache only."""
from pathlib import Path
import json,hashlib,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-3-20261027')
p=B/'LPc_target';assert p.parent==B and not p.is_symlink()
rows={str(f.relative_to(B)):{'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size} for f in p.rglob('*') if f.is_file()}
(B/'LPc_RustObjectHashes.json').write_text(json.dumps(rows,indent=2)+'\n')
size=sum(v['bytes'] for v in rows.values());shutil.rmtree(p)
r={'removed':str(p),'files':len(rows),'bytes':size,'kind':'rebuildable Rust/Kani target cache','keys_generated_or_deleted':False,'shared_tmp_cleanup':'No attributable external-sat/smt2 filename emitted; unrelated shared files untouched','lean_objects':'retained until final audit/admission ends'}
(B/'LPc_RustCleanup.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
