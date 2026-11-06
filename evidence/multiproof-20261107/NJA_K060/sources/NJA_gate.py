"""Owned frozen graph and scratch source validation before EVERY Kani run."""
from pathlib import Path
import sys,json,hashlib,subprocess,os,base64,lzma,difflib
import NJA_stage as stage
E=Path(__file__).resolve().parent;x=json.loads((E/sys.argv[1]).read_text());a=x['attempt'];S=E/'NJA_workspace';out=E/(a+'_validation');out.mkdir(exist_ok=False)
# Only restore our prior scratch harness before re-validating every frozen byte.
p=S/'crates/aspis-r1-cost-probe/src/multiproof.rs';payload=json.loads(lzma.decompress((E/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes()));raw=base64.b64decode(payload[str(p.relative_to(S))]);h=(E/'NJA_harness.rs').read_bytes()
if p.exists():assert stage.sha(p.read_bytes()) in json.loads((E/'NJA_SOURCE_HISTORY.json').read_text()), 'unexpected scratch drift'
p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
for name,info in json.loads((E/'NJA_SUPPLEMENT.json').read_text()).items():
 q=S/name;data=base64.b64decode(info['base64']);assert stage.sha(data)==info['sha256'];assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==info['git_blob'];q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==data
 else:q.write_bytes(data)
# Restore and validate only our recognized statement overlays before the frozen gate.
poseidon=S/'crates/aspis-statement/src/poseidon2.rs';lib=S/'crates/aspis-statement/src/lib.rs'
poseidon_raw=base64.b64decode(payload[str(poseidon.relative_to(S))]);lib_raw=base64.b64decode(payload[str(lib.relative_to(S))])
append=b'\n#[cfg(kani)] mod NJA_native { include!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../NJA_poseidon.rs")); }\n'
lib_patched=lib_raw.replace(b'#![no_std]',b'#![cfg_attr(kani, feature(allocator_api))]\n#![no_std]',1)
assert poseidon.read_bytes() in (poseidon_raw,poseidon_raw+append)
assert lib.read_bytes() in (lib_raw,lib_patched)
poseidon.write_bytes(poseidon_raw);lib.write_bytes(lib_raw)
manifest=stage.validate(S,out,'/home/dombarker/.cargo/bin/cargo');frozen=manifest['files']['Cargo.lock']['sha256'];
from NJA_contract_overlay import overlay
patched=overlay(raw)+b'\n'+h+b'\n'+(E/'NJA_contracts.rs').read_bytes();p.write_bytes(patched)
if x.get('lane')=='poseidon':
 patch=(E/'NJA_KMX.patch').read_bytes();assert stage.sha(patch)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 kmx={'KMX_stubs.rs':'ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138','KMX_native.rs':'cf719c47b5c8c91dcc369984c01bd0b8531b25210e344c9fd06db21b30171880','KMX_CopyMeaning.lean':'2baec49a3446a3bbb2be6f992c97d0a6897534a1cd308db8746194dedf665f2b'}
 if not (S/'KMX_stubs.rs').exists():subprocess.run(['patch','--batch','-p1','-i',str(E/'NJA_KMX.patch')],cwd=S,check=True,stdout=subprocess.DEVNULL)
 for name,pin in kmx.items():assert stage.sha((S/name).read_bytes())==pin
 (S/'NJA_poseidon.rs').write_bytes((E/'NJA_poseidon.rs').read_bytes());poseidon.write_bytes(poseidon_raw+append);lib.write_bytes(lib_patched)
 (out/'NJA_KMX.json').write_text(json.dumps(dict(patch_sha256=stage.sha(patch),files=kmx))+'\n')
assert not any(t in h.decode() for t in ['static mut','UnsafeCell','Atomic','Cell<','RefCell'])
patch=''.join(difflib.unified_diff(raw.decode().splitlines(True),p.read_text().splitlines(True),fromfile='a/'+str(p.relative_to(S)),tofile='b/'+str(p.relative_to(S))))
(out/'NJA_harness.patch').write_text(patch)
(out/'NJA_INPUTS.json').write_text(json.dumps(dict(frozen_revision=stage.REV,harness_sha256=stage.sha(h),patch_sha256=stage.sha(patch.encode()),cargo_target=os.environ['CARGO_TARGET_DIR'],copy_builtins_reached=False,source_sha256=stage.sha(raw),native_command=x['native_command']),indent=2)+'\n')
try:
 r=subprocess.run(x['native_command'],cwd=E)
finally:
 last=stage.sha((S/'Cargo.lock').read_bytes());(out/'NJA_LOCK.json').write_text(json.dumps(dict(before=frozen,after=last,unchanged=last==frozen))+'\n');assert last==frozen,'STOP lock drift';assert p.read_bytes()==patched
sys.exit(r.returncode)
