from pathlib import Path
import json,hashlib,shutil,lzma,base64,difflib,subprocess
B=Path.cwd();P=Path('/home/dombarker/project-offloads/codex-cx-tx2-auth-20261111');S=B/'NNJ_src'
assert not S.exists()
B.mkdir(exist_ok=True)
# Reconstruct archived frozen corpus. No writes to predecessor workspace.
payload=json.loads(lzma.decompress((P/'NMX_FROZEN_PAYLOAD.json.xz').read_bytes()))
manifest=json.loads((P/'NMX_STAGING_MANIFEST.json').read_text())
for rel,value in payload.items():
 p=S/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(value))
for name in ['NMX_FROZEN_PAYLOAD.json.xz','NMX_STAGING_MANIFEST.json','NMX_217_KANI_EXTRA_INPUTS.json','NMX_frozen_graph.sha256','NMX_KMX_copy_stubs.patch']:
 shutil.copy2(P/name,B/name.replace('NMX_','NNJ_',1))
extra=json.loads((B/'NNJ_217_KANI_EXTRA_INPUTS.json').read_text())
for rel,pin in extra['files'].items():
 p=S/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(pin['text'])
 assert hashlib.sha256(p.read_bytes()).hexdigest()==pin['sha256']
patch=B/'NNJ_NMX_base.patch'
subprocess.run(['git','apply','--unsafe-paths',str(patch)],cwd=S,check=True)
# Original exact KMX patch supplies the KMX modules/instrumentation.
subprocess.run(['git','apply',str(B/'NNJ_KMX_copy_stubs.patch')],cwd=S,check=True)
for name in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']:
 shutil.copy2(P/'NMX_src'/name,S/name)
# Check base reconstruction against every frozen source, except original cfg overlay.
allowed={'programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs','crates/aspis-core/src/field.rs'}
for rel,pin in manifest['files'].items():
 if rel not in allowed:assert hashlib.sha256((S/rel).read_bytes()).hexdigest()==pin['sha256'],rel
lane=S/'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs'
lane.write_text(lane.read_text()+'\n#[cfg(kani)] include!("NNJ_lane_arbitrary.rs");\n')
shutil.copy2(B/'NNJ_lane_arbitrary.rs',lane.parent/'NNJ_lane_arbitrary.rs')
native=S/'programs/r1-cost-probe/src/NMX_217_native.rs'
native.write_text(native.read_text()+'\n#[path="NNJ_assignment.rs"] mod NNJ_assignment;\n')
shutil.copy2(B/'NNJ_assignment.rs',native.parent/'NNJ_assignment.rs')
# CARGO_HOME isolates the one modified registry crate; remaining crates symlink read-only.
C=B/'NNJ_cargo';(C/'registry/src').mkdir(parents=True)
for name in ['cache','index']:
 (C/'registry'/name).symlink_to(Path('/home/dombarker/.cargo/registry')/name,target_is_directory=True)
registry_pins={};private=[]
for idx in Path('/home/dombarker/.cargo/registry/src').iterdir():
 if not idx.is_dir():continue
 dest=C/'registry/src'/idx.name;dest.mkdir()
 for package in idx.iterdir():
  out=dest/package.name
  if package.name=='solana-program-error-2.2.2':
   shutil.copytree(package,out);private.append(out)
   original=(out/'src/lib.rs').read_text()
   registry_pins[str(package/'src/lib.rs')]=hashlib.sha256(original.encode()).hexdigest()
   (out/'src/lib.rs').write_text(original+'\n#[cfg(kani)] include!("NNJ_error_arbitrary.rs");\n')
   shutil.copy2(B/'NNJ_error_arbitrary.rs',out/'src/NNJ_error_arbitrary.rs')
  else:out.symlink_to(package,target_is_directory=package.is_dir())
assert private
# Binary tools remain pinned absolute paths; credentials/config not copied.
for name in ['S2W_run_host.py']:
 shutil.copy2(P/name,B/name)
(B/'NNJ_tmp').mkdir();(B/'NNJ_target').mkdir()
# Canonical complete source patch, including inherited NMX+KMX and new constructors.
diffs=[]
for p in sorted(S.rglob('*')):
 if not p.is_file():continue
 rel=str(p.relative_to(S));old=base64.b64decode(payload[rel]) if rel in payload else extra['files'].get(rel,{}).get('text','').encode()
 if old==p.read_bytes():continue
 orig=old.decode();now=p.read_text()
 if orig!=now:diffs.extend(difflib.unified_diff(orig.splitlines(True),now.splitlines(True),fromfile='a/'+rel if orig else '/dev/null',tofile='b/'+rel))
(B/'NNJ_HARNESSES.patch').write_text(''.join(diffs))
regdiff=[]
# Both registry copies have identical original bytes and patch.
p=private[0];orig=(Path(next(iter(registry_pins)))).read_text()
regdiff.extend(difflib.unified_diff(orig.splitlines(True),(p/'src/lib.rs').read_text().splitlines(True),fromfile='a/solana-program-error-2.2.2/src/lib.rs',tofile='b/solana-program-error-2.2.2/src/lib.rs'))
regdiff.extend(difflib.unified_diff([], (p/'src/NNJ_error_arbitrary.rs').read_text().splitlines(True),fromfile='/dev/null',tofile='b/solana-program-error-2.2.2/src/NNJ_error_arbitrary.rs'))
(B/'NNJ_DEPENDENCY.patch').write_text(''.join(regdiff))
files={str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for p in S.rglob('*') if p.is_file()}
regfiles={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for d in private for p in d.rglob('*') if p.is_file()}
x=dict(predecessor=str(P),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_files=files,private_registry_files=regfiles,shared_original_registry=registry_pins,imported_inputs={n:hashlib.sha256((P/n).read_bytes()).hexdigest() for n in ['NMX_FROZEN_PAYLOAD.json.xz','NMX_STAGING_MANIFEST.json','NMX_217_harness.patch','S2W_run_host.py']},KMX_patch_sha256=hashlib.sha256((B/'NNJ_KMX_copy_stubs.patch').read_bytes()).hexdigest())
(B/'NNJ_SEED.json').write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps(dict(source_files=len(files),private_registry_files=len(regfiles),source_patch_sha256=hashlib.sha256((B/'NNJ_HARNESSES.patch').read_bytes()).hexdigest())))
