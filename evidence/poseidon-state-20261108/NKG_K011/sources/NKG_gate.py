"""Owned scratch overlays; frozen graph before EACH Kani and lock after EACH run."""
from pathlib import Path
import importlib.util,json,sys,subprocess,os,base64,lzma,difflib,hashlib
E=Path(__file__).resolve().parent; P=Path('/home/dombarker/project-offloads/codex-cx-multiproof2-20261107')
assert hashlib.sha256((P/'NJE_stage.py').read_bytes()).hexdigest()=='3b05b7c5f1aff94fae52b4b2b50edbdae9c61f6d7bfc4fb8112b543ed8fdc081', 'STOP inherited input drift NJE_stage.py'
assert hashlib.sha256((P/'NJE_SUPPLEMENT.json').read_bytes()).hexdigest()=='1d8b3b2bf561958174ce453f2706adeaae70885cbe73de33576b34683add84eb', 'STOP inherited input drift NJE_SUPPLEMENT.json'
assert hashlib.sha256((P/'NJE_FROZEN_PAYLOAD.json.xz').read_bytes()).hexdigest()=='58902e9cc80f328a57a4348d6470075505388ff034bcceb36a27d1f4c38118c8', 'STOP inherited input drift NJE_FROZEN_PAYLOAD.json.xz'
assert hashlib.sha256((P/'NJE_FROZEN_PAYLOAD.json.sha256').read_bytes()).hexdigest()=='89f8cf69f243878ff24cd659dc6b0269c013ff855af2902578a5e3a76bf9cb39', 'STOP inherited input drift NJE_FROZEN_PAYLOAD.json.sha256'
assert hashlib.sha256((P/'NJE_STAGING_MANIFEST.json').read_bytes()).hexdigest()=='74a894c5ff7f4f3f3dda624b57891e6d7323fb2fa77c2b850d1c1ab4e3f18ad4', 'STOP inherited input drift NJE_STAGING_MANIFEST.json'
spec=importlib.util.spec_from_file_location('NKG_frozen_stage',P/'NJE_stage.py');stage=importlib.util.module_from_spec(spec);spec.loader.exec_module(stage)
x=json.loads((E/sys.argv[1]).read_text());a=x['attempt'];S=E/'NKG_workspace';out=E/(a+'_validation');out.mkdir(exist_ok=False)
payload=json.loads(lzma.decompress((P/'NJE_FROZEN_PAYLOAD.json.xz').read_bytes()))
mods={}
for rel in ['crates/aspis-statement/src/state_only_poseidon.rs','crates/aspis-statement/src/lib.rs','crates/aspis-r1-cost-probe/src/lib.rs']:
 raw=base64.b64decode(payload[rel]);q=S/rel
 if rel.endswith('state_only_poseidon.rs'):patched=raw+b'\n#[cfg(kani)] mod NKG_native { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../NKG_state_native.rs")); }\n'

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
(out/'NKG_TARGET_METADATA.stderr').write_text(m.stderr);assert m.returncode==0,m.stderr
meta=json.loads(next(line for line in m.stdout.splitlines() if line.startswith('{')))
pkgs={p['id']:p for p in meta['packages']};frozen_keys={(p['name'],p['version'],p.get('source')) for p in __import__('tomllib').loads((S/'Cargo.lock').read_text())['package']}
assert all((p['name'],p['version'],p.get('source')) in frozen_keys for p in meta['packages'])
features=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],features=n['features']) for n in meta['resolve']['nodes']]
frozen_packages={(p['name'],p['version'],p.get('source')):p for p in __import__('tomllib').loads((S/'Cargo.lock').read_text())['package']}
edge_errors=[]
for n in meta['resolve']['nodes']:
 p=pkgs[n['id']];expected=frozen_packages[(p['name'],p['version'],p.get('source'))]
 for dep in n['dependencies']:
  q=pkgs[dep];labels=[label.split(' ') for label in expected.get('dependencies',[])]
  if not any(v[0]==q['name'] and (len(v)<2 or v[1]==q['version']) and (len(v)<3 or v[2].strip('()')==q.get('source')) for v in labels):edge_errors.append([p['name'],q['name']])
assert not edge_errors,'STOP actual-target edge drift'

target_name='aspis-r1-cost-probe' if x.get('lane')=='multiproof' else 'aspis-statement'
requested=set(target_features.split(','));actual=set(next(n['features'] for n in features if n['name']==target_name));assert requested<=actual
expected_statement=next(n['features'] for n in json.loads((out/'NHR_GRAPH_CHECK.json').read_text())['features'] if n['name']=='aspis-statement')
assert next(n['features'] for n in features if n['name']=='aspis-statement')==expected_statement
assert stage.sha((S/'Cargo.lock').read_bytes())==frozen
(out/'NKG_TARGET_GRAPH.json').write_text(json.dumps(dict(command=meta_cmd,features=features,lock_unchanged=True,packages_frozen=True,edge_errors=edge_errors,graph_matches_frozen=True,helper_target_reason='Statement helper, with exact deployed statement features; no entrypoint feature suppressed'),indent=2)+'\n')

patch=(P/'NJE_KMX.patch').read_bytes();assert stage.sha(patch)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
if not (S/'KMX_stubs.rs').exists():subprocess.run(['patch','--batch','-p1','-i',str(P/'NJE_KMX.patch')],cwd=S,check=True,stdout=subprocess.DEVNULL)
assert stage.sha((S/'KMX_stubs.rs').read_bytes())=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
h=(E/'NKG_state_native.rs').read_bytes();assert not any(t in h.decode() for t in ['static mut','UnsafeCell','Atomic','Cell<','RefCell'])
(S/'NKG_state_native.rs').write_bytes(h)
diff=''
for rel,(raw,patched) in mods.items():
 (S/rel).write_bytes(patched);diff+=''.join(difflib.unified_diff(raw.decode().splitlines(True),patched.decode().splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
diff+=''.join(difflib.unified_diff([],h.decode().splitlines(True),fromfile='/dev/null',tofile='b/NKG_state_native.rs'))
(out/'NKG_harness.patch').write_text(diff)
(out/'NKG_INPUTS.json').write_text(json.dumps(dict(frozen_revision=stage.REV,harness_sha256=stage.sha(h),KMX_patch_sha256=stage.sha(patch),cargo_target=os.environ['CARGO_TARGET_DIR'],native_command=x['native_command'],inherited_stage_sha256=stage.sha((P/'NJE_stage.py').read_bytes())),indent=2)+'\n')
try:r=subprocess.run(x['native_command'],cwd=E,env={**os.environ,'CARGO_NET_OFFLINE':'true'})
finally:
 last=stage.sha((S/'Cargo.lock').read_bytes());(out/'NKG_LOCK.json').write_text(json.dumps(dict(before=frozen,after=last,unchanged=last==frozen))+'\n');assert last==frozen,'STOP lock drift'
 for rel,(_,patched) in mods.items():assert (S/rel).read_bytes()==patched
sys.exit(r.returncode)
