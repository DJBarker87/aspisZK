from pathlib import Path
import hashlib,json,subprocess,difflib
B=Path(__file__).resolve().parent;S=B/'NKM_workspace'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((B/'NKM_STAGING_MANIFEST.json').read_text())
assert all(sha(S/n)==r['sha256'] for n,r in manifest['files'].items())
patch=B/'NKM_KMX_copy_stubs.patch'
assert sha(patch)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
subprocess.run(['git','apply','--check',str(patch)],cwd=S,check=True)
subprocess.run(['git','apply',str(patch)],cwd=S,check=True)
rel='crates/aspis-r1-cost-probe/src/lib.rs';p=S/rel;before=p.read_text();after='#![cfg_attr(kani,feature(allocator_api))]\n'+before+'\n#[cfg(kani)]\nmod NKM_native;\n';p.write_text(after)
n='crates/aspis-r1-cost-probe/src/NKM_native.rs';(S/n).write_text((B/'NKM_native_generated.rs.txt').read_text())
text=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
text+=''.join(difflib.unified_diff([], (S/n).read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+n))
(B/'NKM_harness.patch').write_text(text)
pins={n:sha(S/n) for n in [rel,n,'KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean','Cargo.lock','Cargo.toml']}
frozen={n:r['sha256'] for n,r in manifest['files'].items() if n not in pins}
(B/'NKM_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');(B/'NKM_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2)+'\n')
(B/'NKM_NATIVE_SETUP.json').write_text(json.dumps(dict(source_bytes=sum(p.stat().st_size for p in S.rglob('*')if p.is_file()),frozen_paths=len(frozen),patch_sha256=sha(B/'NKM_harness.patch'),kmx_patch_sha256=sha(patch),CARGO_TARGET_DIR=str(B/'NKM_target')),indent=2)+'\n')
print('Frozen source pinned; exact KMX patch and cfg-only harness installed')
