#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
base=Path(__file__).resolve().parent
sysroot=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
old=base.parent/'codex-cx-s2-trust-20261023/lean-olean-manifest.json'
manifest=json.loads(old.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mismatches=[p for p,h in manifest.items() if sha(sysroot/p)!=h]
assert not mismatches,mismatches
kani=Path('/home/dombarker/.kani/kani-0.67.0')
result=dict(imported_sysroot_manifest=str(old),manifest_file_sha256=sha(old),olean_count=len(manifest),all_cached_objects_match=True,lean_binary_sha256=sha(sysroot/'bin/lean'),kani_compiler_sha256=sha(kani/'bin/kani-compiler'),cbmc_sha256=sha(kani/'bin/cbmc'),kani_rustc=subprocess.check_output([str(kani/'toolchain/bin/rustc'),'--version'],text=True).strip(),inspection_only=True)
(base/'S2H-tool-pins.json').write_text(json.dumps(result,indent=2)+'\n')
