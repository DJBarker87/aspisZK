#!/usr/bin/env python3
"""Read-only hashes of exact private inputs/tools/objects; no proof replay."""
from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-s2c-20261023')
def pin(p):
 return {'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size}
paths=[Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler'),Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')]
paths+=list(H.glob('*.olean'))+[H/'kani-native/Cargo.lock',H/'native-source/Cargo.toml']
paths+=list(Path('/home/dombarker/.cargo/registry/src').glob('*/solana-program-entrypoint-2.3.0/src/lib.rs'))
manifest=json.loads((H/'native-dependencies.json').read_text())
assert all(pin(H/'native-source'/p)['sha256']==sha for p,sha in manifest.items())
info={'files':{str(p):pin(p) for p in paths if p.is_file()},'native_dependency_manifest':pin(H/'native-dependencies.json'),'all_native_sources_match':True,'kani_outputs':{str(p.relative_to(H)):pin(p) for p in (H/'kani-target').rglob('*') if p.is_file() and p.name.endswith(('.kani-metadata.json','.out'))},'scope':'Hashes only. No binary artifact is committed. Native SDK/ABI/caller interpretation remains open.'}
(H/'host-inventory.json').write_text(json.dumps(info,indent=2)+'\n')
