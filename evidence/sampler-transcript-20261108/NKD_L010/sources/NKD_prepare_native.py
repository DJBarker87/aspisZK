from pathlib import Path
import json,hashlib,shutil,difflib
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-transcript-scalars-20261105');S=B/'NKD_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((B/'NKD_NGT_SOURCE_PINS.json').read_text())
for n,h in old.items():assert sha(P/'NGT_src'/n)==h,('changed predecessor scratch',n)
assert not S.exists(),'Never create second scratch copy'
shutil.copytree(P/'NGT_src',S)
assert sha(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
rel='programs/r1-cost-probe/src/lib.rs';p=S/rel;before=p.read_text();after='#![cfg_attr(kani,feature(allocator_api))]\n'+before+'\n#[cfg(kani)]\nmod NKD_native;\n';p.write_text(after)
(S/'programs/r1-cost-probe/src/NKD_native.rs').write_bytes((B/'NKD_native_generated.rs.txt').read_bytes())
patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
patch+=''.join(difflib.unified_diff([], (S/'programs/r1-cost-probe/src/NKD_native.rs').read_text().splitlines(True),fromfile='/dev/null',tofile='b/programs/r1-cost-probe/src/NKD_native.rs'))
(B/'NKD_harness.patch').write_text(patch)
pins={str(p.relative_to(S)):sha(p) for p in sorted(S.rglob('*')) if p.is_file()}
(B/'NKD_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
# Frozen validation omits only files whose exact overlays are in source_pins.
frozen=json.loads((B/'NKD_NGT_FROZEN_FILE_PINS.json').read_text());frozen={n:h for n,h in frozen.items()if n not in old and n!=rel}
(B/'NKD_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=1)+'\n')
(B/'NKD_NATIVE_SETUP.json').write_text(json.dumps(dict(source_files=len(pins),source_bytes=sum(p.stat().st_size for p in S.rglob('*')if p.is_file()),seed_source=str(P/'NGT_src'),seed_pins_sha256=sha(B/'NKD_NGT_SOURCE_PINS.json'),lock_sha256=sha(S/'Cargo.lock'),patch_sha256=sha(B/'NKD_harness.patch'),disk=shutil.disk_usage(B)._asdict(),CARGO_TARGET_DIR=str(B/'NKD_target')),indent=1)+'\n')
print('Native scratch copied, pinned and overlaid; no compiler launch')
