"""Second immutable dependency identity: unchanged original lib, renamed package."""
from pathlib import Path
import shutil,hashlib,json
D=Path(__file__).resolve().parent
R=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.1')
T=D/'vendor/zeroize-original';assert T.exists()
assert (R/'src/lib.rs').read_bytes()==(D/'zeroize-original.rs.txt').read_bytes()
# Complete only an exact pristine copy left by the pre-build manifest guard.
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert {str(p.relative_to(R)):sha(p) for p in R.rglob('*') if p.is_file()} == {str(p.relative_to(T)):sha(p) for p in T.rglob('*') if p.is_file()}
p=T/'Cargo.toml';before=p.read_text()
# Rename only the package; preserve [lib] name so Cargo dependency alias resolves it.
header=before.index('[package]');end=before.index('\n[',header+1)
a=before[header:end];assert a.count('name = "zeroize"')==1
p.write_text(before[:header]+a.replace('name = "zeroize"','name = "prover-rw-resume-scalar-zeroize-original"')+before[end:])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
original={str(p.relative_to(R)):sha(p) for p in R.rglob('*') if p.is_file()}
job={str(p.relative_to(T)):sha(p) for p in T.rglob('*') if p.is_file()}
assert [p for p in original if original[p]!=job[p]]==['Cargo.toml']
(D/'erasure-package-identity.json').write_text(json.dumps(dict(upstream_files=original,job_files=job,changed_path='Cargo.toml',reason='distinct Cargo path package identity; source lib unchanged'),indent=2)+'\n')
