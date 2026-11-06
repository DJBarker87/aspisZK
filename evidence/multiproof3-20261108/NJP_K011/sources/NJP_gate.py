"""Owned scratch overlays; frozen graph before EACH Kani and lock after EACH run."""
from pathlib import Path
import importlib.util,json,sys,subprocess,os,base64,lzma,difflib,hashlib
E=Path(__file__).resolve().parent; P=Path('/home/dombarker/project-offloads/codex-cx-multiproof2-20261107')
spec=importlib.util.spec_from_file_location('NJP_frozen_stage',P/'NJE_stage.py');stage=importlib.util.module_from_spec(spec);spec.loader.exec_module(stage)
x=json.loads((E/sys.argv[1]).read_text());a=x['attempt'];S=E/'NJP_workspace';out=E/(a+'_validation');out.mkdir(exist_ok=False)
payload=json.loads(lzma.decompress((P/'NJE_FROZEN_PAYLOAD.json.xz').read_bytes()))
mods={}
for rel in ['crates/aspis-statement/src/poseidon2.rs','crates/aspis-statement/src/lib.rs']:
 raw=base64.b64decode(payload[rel]);q=S/rel
 if rel.endswith('poseidon2.rs'):patched=raw+b'\n#[cfg(kani)] mod NJP_native { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../NJP_poseidon.rs")); }\n'
 else:patched=raw.replace(b'#![no_std]',b'#![cfg_attr(kani, feature(allocator_api))]\n#![no_std]',1)
 if q.exists():assert q.read_bytes() in (raw,patched),'STOP unknown scratch drift'
 q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw);mods[rel]=(raw,patched)
for name,info in json.loads((P/'NJE_SUPPLEMENT.json').read_text()).items():
 q=S/name;data=base64.b64decode(info['base64']);assert stage.sha(data)==info['sha256'];q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==data
 else:q.write_bytes(data)
manifest=stage.validate(S,out,'/home/dombarker/.cargo/bin/cargo');frozen=manifest['files']['Cargo.lock']['sha256']
# Record the actual Kani target's resolved feature graph, not only the verifier
# parity baseline. Both are frozen-lock offline resolutions, before compilation.
cmd=x['native_command'];target_manifest=cmd[cmd.index('--manifest-path')+1];target_features=cmd[cmd.index('--features')+1]
meta_cmd=['/home/dombarker/.cargo/bin/cargo','+1.94.1','metadata','--manifest-path',target_manifest,'--locked','--offline','--format-version','1','--features',target_features]
m=subprocess.run(meta_cmd,capture_output=True,text=True,env={**os.environ,'CARGO_NET_OFFLINE':'true'})
(out/'NJP_TARGET_METADATA.stderr').write_text(m.stderr);assert m.returncode==0,m.stderr
meta=json.loads(next(line for line in m.stdout.splitlines() if line.startswith('{')))
pkgs={p['id']:p for p in meta['packages']};frozen_keys={(p['name'],p['version'],p.get('source')) for p in __import__('tomllib').loads((S/'Cargo.lock').read_text())['package']}
assert all((p['name'],p['version'],p.get('source')) in frozen_keys for p in meta['packages'])
features=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],features=n['features']) for n in meta['resolve']['nodes']]
assert next(n['features'] for n in features if n['name']=='aspis-statement')==sorted(target_features.split(','))
assert stage.sha((S/'Cargo.lock').read_bytes())==frozen
(out/'NJP_TARGET_GRAPH.json').write_text(json.dumps(dict(command=meta_cmd,features=features,lock_unchanged=True,packages_frozen=True,helper_target_reason='Statement helper, with exact deployed statement features; no entrypoint feature suppressed'),indent=2)+'\n')

patch=(P/'NJE_KMX.patch').read_bytes();assert stage.sha(patch)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
if not (S/'KMX_stubs.rs').exists():subprocess.run(['patch','--batch','-p1','-i',str(P/'NJE_KMX.patch')],cwd=S,check=True,stdout=subprocess.DEVNULL)
assert stage.sha((S/'KMX_stubs.rs').read_bytes())=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
h=(E/'NJP_poseidon.rs').read_bytes();assert not any(t in h.decode() for t in ['static mut','UnsafeCell','Atomic','Cell<','RefCell'])
(S/'NJP_poseidon.rs').write_bytes(h)
diff=''
for rel,(raw,patched) in mods.items():
 (S/rel).write_bytes(patched);diff+=''.join(difflib.unified_diff(raw.decode().splitlines(True),patched.decode().splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
diff+=''.join(difflib.unified_diff([],h.decode().splitlines(True),fromfile='/dev/null',tofile='b/NJP_poseidon.rs'))
(out/'NJP_harness.patch').write_text(diff)
(out/'NJP_INPUTS.json').write_text(json.dumps(dict(frozen_revision=stage.REV,harness_sha256=stage.sha(h),KMX_patch_sha256=stage.sha(patch),cargo_target=os.environ['CARGO_TARGET_DIR'],native_command=x['native_command'],inherited_stage_sha256=stage.sha((P/'NJE_stage.py').read_bytes())),indent=2)+'\n')
try:r=subprocess.run(x['native_command'],cwd=E,env={**os.environ,'CARGO_NET_OFFLINE':'true'})
finally:
 last=stage.sha((S/'Cargo.lock').read_bytes());(out/'NJP_LOCK.json').write_text(json.dumps(dict(before=frozen,after=last,unchanged=last==frozen))+'\n');assert last==frozen,'STOP lock drift'
 for rel,(_,patched) in mods.items():assert (S/rel).read_bytes()==patched
sys.exit(r.returncode)
