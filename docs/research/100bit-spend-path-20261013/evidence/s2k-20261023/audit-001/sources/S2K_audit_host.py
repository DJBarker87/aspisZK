"""Read-only final source, compiler and imported cache pin audit."""
from pathlib import Path
import hashlib,json,subprocess
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected=json.loads((B/'native-source.json').read_text())
mismatch=[f for f,v in expected.items() if sha(B/'native-source'/f)!=v['sha256']]
assert not mismatch,mismatch
kani=Path('/home/dombarker/.kani/kani-0.67.0');lean=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
toolpaths=[kani/'bin/kani-compiler',kani/'bin/cbmc',kani/'toolchain/bin/rustc',lean/'bin/lean',lean/'bin/lake',Path('/home/dombarker/.cargo/bin/cargo-kani')]
# The exact inherited inventory is already source-controlled as G/I shards.
pins=Path('/home/dombarker/project-offloads/codex-cx-s2i-20261023/lean-011-objects.json')
objects=json.loads(pins.read_text());object_mismatch=[]
# Verify the actual direct S2I runtime-law module and every selected object.
for k,v in objects.items():
 p=Path(v['path'])
 if not p.is_file() or sha(p)!=v['sha256']:object_mismatch.append(k)
lock=B/'S2K-native/Cargo.lock'
result=dict(kind='read-only audit',native_source_files=len(expected),native_source_manifest_sha256=sha(B/'native-source.json'),native_sources_all_match=not mismatch,native_workspace_sha256=sha(B/'native-source/Cargo.toml'),cargo_lock_sha256=sha(lock),cargo_lock_bytes=lock.stat().st_size,tools={str(p):dict(sha256=sha(p),bytes=p.stat().st_size) for p in toolpaths},rustc=subprocess.check_output([str(kani/'toolchain/bin/rustc'),'--version'],text=True).strip(),lean=subprocess.check_output([str(lean/'bin/lean'),'--version'],text=True).strip(),inherited_selected_objects=dict(inventory=str(pins),inventory_sha256=sha(pins),count=len(objects),all_match=not object_mismatch,mismatches=object_mismatch),own_remaining_processes=[line for line in subprocess.check_output(['ps','-eo','pid,args'],text=True).splitlines() if str(B) in line and ('cbmc ' in line or 'cargo-kani ' in line or '/bin/lean ' in line)],print_axioms='N/A: read-only audit')
(B/'host-audit.json').write_text(json.dumps(result,indent=2)+'\n');assert not object_mismatch,object_mismatch
print(json.dumps({k:result[k] for k in ['native_source_files','native_sources_all_match','own_remaining_processes']}))
