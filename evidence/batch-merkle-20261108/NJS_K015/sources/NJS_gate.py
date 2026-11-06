"""Owned frozen-graph/offline Kani runner. No shared infrastructure changes."""
from pathlib import Path
import sys,json,hashlib,subprocess,os,base64,lzma,difflib
import NJS_NHR_stage as stage
E=Path(__file__).resolve().parent;x=json.loads((E/sys.argv[1]).read_text());a=x['attempt'];S=E/'NJS_workspace';out=E/(a+'_validation');out.mkdir(exist_ok=False)
payload=json.loads(lzma.decompress((E/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes()))
p=S/'crates/aspis-r1-cost-probe/src/candidate.rs';raw=base64.b64decode(payload[str(p.relative_to(S))]);append=b'\n#[cfg(kani)] mod NJS_native { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../NJS_harness.rs")); }\n'
if p.exists():assert p.read_bytes() in (raw,raw+append),'STOP unknown scratch drift'
p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
for name,info in json.loads((E/'NJS_SUPPLEMENT.json').read_text()).items():
 q=S/name;data=base64.b64decode(info['base64']);assert stage.sha(data)==info['sha256'];assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==info['git_blob'];q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==data
 else:q.write_bytes(data)
lib=S/'crates/aspis-r1-cost-probe/src/lib.rs';lib_raw=base64.b64decode(payload[str(lib.relative_to(S))]);lib_patched=lib_raw.replace(b'#![no_std]',b'#![cfg_attr(kani, feature(allocator_api))]\n#![no_std]',1)
if lib.exists():assert lib.read_bytes() in (lib_raw,lib_patched),'STOP unknown scratch root drift'
lib.parent.mkdir(parents=True,exist_ok=True);lib.write_bytes(lib_raw)
manifest=stage.validate(S,out,'/home/dombarker/.cargo/bin/cargo');frozen=manifest['files']['Cargo.lock']['sha256']
patch=(E/'NJS_KMX.patch').read_bytes();assert stage.sha(patch)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
if not (S/'KMX_stubs.rs').exists():subprocess.run(['patch','--batch','-p1','-i',str(E/'NJS_KMX.patch')],cwd=S,check=True,stdout=subprocess.DEVNULL)
assert stage.sha((S/'KMX_stubs.rs').read_bytes())=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
frag=(E/'NJS_fragments.rs').read_bytes(); assoc=json.loads((E/'NJS_FRAGMENT_ASSOCIATION.json').read_text()); body=assoc['selected_body'];assert stage.sha(body.encode())==assoc['body_sha256'];assert body in raw.decode();assert body in frag.decode();(S/'NJS_fragments.rs').write_bytes(frag)
h=(E/'NJS_harness.rs').read_bytes();assert not any(t in h.decode() for t in ['static mut','UnsafeCell','Atomic'])
(S/'NJS_harness.rs').write_bytes(h);p.write_bytes(raw+append);lib.write_bytes(lib_patched)
diff=''.join(difflib.unified_diff(raw.decode().splitlines(True),(raw+append).decode().splitlines(True),fromfile='a/'+str(p.relative_to(S)),tofile='b/'+str(p.relative_to(S))))
libdiff=''.join(difflib.unified_diff(lib_raw.decode().splitlines(True),lib_patched.decode().splitlines(True),fromfile='a/'+str(lib.relative_to(S)),tofile='b/'+str(lib.relative_to(S))))
(out/'NJS_harness.patch').write_text(diff+libdiff+'\n'+''.join(difflib.unified_diff([],h.decode().splitlines(True),fromfile='/dev/null',tofile='b/NJS_harness.rs')))
(out/'NJS_INPUTS.json').write_text(json.dumps(dict(frozen_revision=stage.REV,harness_sha256=stage.sha(h),patch_sha256=stage.sha(diff.encode()),KMX_patch_sha256=stage.sha(patch),cargo_target=os.environ['CARGO_TARGET_DIR'],source_sha256=stage.sha(raw),native_command=x['native_command']),indent=2)+'\n')
try:r=subprocess.run(x['native_command'],cwd=E,env={**os.environ,'CARGO_NET_OFFLINE':'true'})
finally:
 last=stage.sha((S/'Cargo.lock').read_bytes());(out/'NJS_LOCK.json').write_text(json.dumps(dict(before=frozen,after=last,unchanged=last==frozen))+'\n');assert last==frozen,'STOP lock drift';assert p.read_bytes()==raw+append
sys.exit(r.returncode)
