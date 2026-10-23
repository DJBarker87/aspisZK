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
# Verify the current focused DAG as well as inherited caches. Older successful
# versions of an edited module are retained receipts, not current object claims.
own={}
for receipt in sorted(B.glob('lean-*/receipt.json')):
 x=json.loads(receipt.read_text())
 if x['exit_status']!=0:continue
 src=x['sources'][0]
 if not (B/src).is_file() or sha(B/src)!=x['source_hashes'][src]:continue
 obj=(B/src).with_suffix('.olean')
 assert obj.is_file(),obj
 for dep in x['deps_fingerprint']['selected_objects'].values():
  assert sha(Path(dep['path']))==dep['sha256'],(receipt,dep['path'])
 own[src]=dict(receipt=str(receipt.relative_to(B)),source_sha256=sha(B/src),object_sha256=sha(obj),object_bytes=obj.stat().st_size,direct_dependencies_all_match=True)
assert 'S2K_Exports.lean' in own
codec=json.loads((B/'extract-011.json').read_text())['deps_fingerprint']['tools']
for path,pin in codec.items():assert sha(Path(path))==pin['sha256'],path
nightly=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc')
if nightly.exists():toolpaths.append(nightly)
for path in codec:
 if Path(path) not in toolpaths:toolpaths.append(Path(path))
lock=B/'S2K-native/Cargo.lock'
result=dict(kind='read-only audit',native_source_files=len(expected),native_source_manifest_sha256=sha(B/'native-source.json'),native_sources_all_match=not mismatch,native_workspace_sha256=sha(B/'native-source/Cargo.toml'),cargo_lock_sha256=sha(lock),cargo_lock_bytes=lock.stat().st_size,tools={str(p):dict(sha256=sha(p),bytes=p.stat().st_size) for p in toolpaths},rustc=subprocess.check_output([str(kani/'toolchain/bin/rustc'),'--version'],text=True).strip(),lean=subprocess.check_output([str(lean/'bin/lean'),'--version'],text=True).strip(),focused_current_modules=own,codec_tools_all_match=True,inherited_selected_objects=dict(inventory=str(pins),inventory_sha256=sha(pins),count=len(objects),all_match=not object_mismatch,mismatches=object_mismatch),own_remaining_processes=[line for line in subprocess.check_output(['ps','-eo','pid,args'],text=True).splitlines() if str(B) in line and ('cbmc ' in line or 'cargo-kani ' in line or '/bin/lean ' in line)],print_axioms='N/A: read-only audit')
(B/'host-audit.json').write_text(json.dumps(result,indent=2)+'\n');assert not object_mismatch,object_mismatch
print(json.dumps({k:result[k] for k in ['native_source_files','native_sources_all_match','own_remaining_processes']}))
