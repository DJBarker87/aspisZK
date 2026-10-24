"""Post-run artifact/source assessment only; not a new identity or proof gate."""
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=[]
for p in [Path('/home/dombarker/.kani/kani-0.67.0/bin'),Path('/home/dombarker/.kani/kani-0.67.0/lib'),D/'target/kani']:
    if p.exists():paths += [q for q in p.rglob('*') if q.is_file() and q.suffix in ['.rlib','.rmeta','.out','.symtab','.json'] or q.is_file() and q.parent==p]
paths += [Path(p) for p in ['/home/dombarker/.cargo/bin/cargo-kani','/home/dombarker/.cargo/bin/cargo','/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','/usr/bin/python3','/usr/bin/timeout','/usr/bin/time']]
rows=[]
for p in sorted(set(paths)):
    rows.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
deps={}
for p in (D/'target').rglob('zeroize-*.d'):
    deps[str(p)]=p.read_text()
(D/'postrun-artifacts.json').write_text(json.dumps(dict(assessment='Post-run hashes and dependency path assessment, not a fresh ELF gate or a replay. Kani fence is sequential; aliasing/provenance argument is separately stated.',artifacts=rows,dependency_records=deps,print_axioms='N/A: read-only artifact audit'),indent=2)+'\n')
for registry in Path('/home/dombarker/.cargo/registry/src').glob('*/zeroize-1.8.1/src/lib.rs'):
    name=registry.parents[2].name
    (D/f'zeroize-1.8.1-{name}.rs.txt').write_bytes(registry.read_bytes())
(D/'tool-versions.txt').write_text(subprocess.run(['/home/dombarker/.cargo/bin/rustc','-Vv'],capture_output=True,text=True).stdout+subprocess.run(['/home/dombarker/.cargo/bin/cargo-kani','--version'],capture_output=True,text=True).stdout)
print(json.dumps({'artifact_count':len(rows),'zeroize_dependency_records':len(deps)}))
