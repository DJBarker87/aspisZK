"""Prepare own package copies after diagnostic, without compiler invocation."""
from pathlib import Path
import shutil,json,hashlib
D=Path(__file__).resolve().parent
assert json.loads((D/'packet/readonly/diagnostic.json').read_text())['allowed']
R=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for name,snapshot,dest in [('zeroize-1.8.1','zeroize','src/lib.rs'),('getrandom-0.3.4','getrandom-error','src/error.rs'),('zeroize-original','zeroize','src/lib.rs')]:
 original=R/('zeroize-1.8.1' if name=='zeroize-original' else name)
 target=D/'vendor'/name
 assert not target.exists()
 assert (original/dest).read_bytes()==(D/(snapshot+'-original.rs.txt')).read_bytes()
 shutil.copytree(original,target)
 if name=='zeroize-original':
  p=target/'Cargo.toml';s=p.read_text();assert s.count('name = "zeroize"')==1
  p.write_text(s.replace('name = "zeroize"','name = "prover-rw-resume-scalar-zeroize-original"'))
 else:(target/dest).write_bytes((D/(snapshot+'-instrumented.rs.txt')).read_bytes())
 before={str(p.relative_to(original)):sha(p) for p in original.rglob('*') if p.is_file()}
 after={str(p.relative_to(target)):sha(p) for p in target.rglob('*') if p.is_file()}
 changed=[p for p in before if before[p]!=after[p]]
 assert changed==(['Cargo.toml'] if name=='zeroize-original' else [dest])
 rows.append(dict(package=name,upstream_files=before,job_files=after,changed=changed))
(D/'package-identity.json').write_text(json.dumps(rows,indent=2)+'\n')
