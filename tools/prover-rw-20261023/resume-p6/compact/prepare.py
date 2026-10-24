"""Prepare only this job's vendor copies; refuse replacing any existing package."""
from pathlib import Path
import shutil,hashlib,json
D=Path(__file__).resolve().parent
R=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
rows=[]
for name,src,dest in [('zeroize-1.8.1','zeroize','src/lib.rs'),('getrandom-0.3.4','getrandom-error','src/error.rs')]:
 original=R/name;target=D/'vendor'/name
 assert not target.exists(),target
 assert (original/dest).read_bytes()==(D/(src+'-original.rs.txt')).read_bytes()
 shutil.copytree(original,target)
 before={str(p.relative_to(original)):hashlib.sha256(p.read_bytes()).hexdigest() for p in original.rglob('*') if p.is_file()}
 (target/dest).write_bytes((D/(src+'-instrumented.rs.txt')).read_bytes())
 after={str(p.relative_to(target)):hashlib.sha256(p.read_bytes()).hexdigest() for p in target.rglob('*') if p.is_file()}
 assert [p for p in before if before[p]!=after[p]]==[dest]
 rows.append(dict(package=name,upstream_files=before,job_files=after,changed_path=dest))
(D/'package-identity.json').write_text(json.dumps(rows,indent=2)+'\n')
