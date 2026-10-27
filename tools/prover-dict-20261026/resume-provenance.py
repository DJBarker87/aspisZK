"""Read-only input/tool pin collection, not launch/monitor infrastructure."""
from pathlib import Path
import hashlib,json,subprocess
h=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026');r=h/'src';k=Path('/home/dombarker/.kani/kani-0.67.0');sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
paths=list((r/'tools/prover-dict-20261026').rglob('*.rs'))+list((r/'tools/prover-dict-20261026').rglob('Cargo.toml'))+list((r/'tools/prover-dict-20261026').rglob('Cargo.lock'))
paths += [p for p in (k/'bin').glob('*') if p.is_file()]
paths += [k/'toolchain/bin/rustc',k/'rustc-version',k/'rust-toolchain-version']
paths += [p for p in k.rglob('libcore-*.rlib') if p.is_file()]
paths += [p for p in k.rglob('libstd-*.rlib') if p.is_file()]
rows=[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(set(paths)) if p.is_file()]
result=dict(inputs=rows,kani_rustc=subprocess.check_output([str(k/'toolchain/bin/rustc'),'-Vv'],text=True),warning='Historical runner toolchain field prints ambient rustc, not Kani embedded rustc. Kani runtime uses its pinned embedded 1.93 nightly; Charon uses its separately pinned nightly2026-06-01. Scoped native std checks do not establish resource/dynamic-carrier equivalence across compilers or a release artifact connection.',print_axioms='N/A: read-only input/tool provenance; no binary content copied')
(h/'receipts/resume-provenance.json').write_text(json.dumps(result,indent=2)+'\n');print(len(rows),'pins')
