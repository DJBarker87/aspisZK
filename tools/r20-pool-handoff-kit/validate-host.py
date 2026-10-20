#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
H=Path('/home/dombarker/project-offloads/codex-cx-r20-pool-20261020')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((H/'harness/input-hashes.json').read_text())
rows=[p for p,h in pins.items() if not (H/'src'/p).is_file() or sha(H/'src'/p)!=h]
assert not rows,rows
expected={'programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/pair_forest_dispatch.rs'}
test_delta=[p for p,h in pins.items() if sha(H/'test-src'/p)!=h]
assert set(test_delta)==expected,test_delta
native=[p for p in (H/'test-target/release/deps').glob('aspis_pool-*') if p.is_file() and p.suffix=='' and p.stat().st_mode & 0o111]
out=dict(native_test_binaries={str(p.relative_to(H)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in native},checked_files=len(pins),mismatches=rows,test_only_instrumented_files=test_delta,source_revision=(H/'source-revision.txt').read_text().strip(),versions={n:subprocess.check_output(c,text=True).strip() for n,c in {'rustc':['/home/dombarker/.cargo/bin/rustc','--version'],'cargo':['/home/dombarker/.cargo/bin/cargo','--version'],'host':['uname','-a']}.items()},llbc={})
for p in sorted(H.glob('extraction-*/*.llbc')):
 d=json.loads(p.read_text());out['llbc'][str(p.relative_to(H))]=dict(sha256=sha(p),bytes=p.stat().st_size,has_errors=d['has_errors']);assert not d['has_errors']
(H/'source-validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(checked_files=len(pins),mismatches=rows)))
