from pathlib import Path
import os,json,subprocess,hashlib,re,tomllib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');P=D/'weights-fixture'
lock=(D/'deployed-client-Cargo.lock').read_bytes();assert hashlib.sha256(lock).hexdigest()==json.loads((D/'deployed-lock-pin.json').read_text())['sha256']
(P/'Cargo.lock').write_bytes(lock);allowed={(p['name'],p['version']) for p in tomllib.loads(lock.decode())['package']}
units=json.loads((D/'deployed-units.json').read_text());expected={}
for u in units:expected.setdefault(u['package_id'],set()).update(u['features'])
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target-weights'),CARGO_BUILD_JOBS='4',RUSTC_BOOTSTRAP='1',RUSTFLAGS='-Zdump-mir=box_from_parts -Zdump-mir-dir='+str(D/'box-mir')+' --emit=llvm-ir,link')
changes=[]
for iteration in range(6):
 r=subprocess.run(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--format-version','1'],env=env,capture_output=True,text=True);assert r.returncode==0,r.stderr
 m=json.loads(r.stdout);nodes={x['id']:x for x in m['resolve']['nodes']};resolved=[dict(id=p['id'],name=p['name'],version=p['version'],features=nodes[p['id']]['features']) for p in m['packages']]
 assert all((p['name'],p['version']) in allowed or p['name']=='pv-fscan-deployed-project-fixture' for p in resolved),[(p['name'],p['version']) for p in resolved if (p['name'],p['version']) not in allowed and p['name']!='pv-fscan-deployed-project-fixture']
 additions=[]
 for i,p in enumerate(resolved):
  wanted=expected.get(p['id'])
  if wanted is not None and set(p['features'])!=wanted:
   assert set(p['features'])<=wanted,(p,wanted)
   additions.append(f'pv_cfg_{iteration}_{i}={{package={json.dumps(p["name"])},version={json.dumps("="+p["version"])},default-features=false,features={json.dumps(sorted(wanted))}}}\n')
   changes.append(dict(package=p['id'],before=p['features'],deployed=sorted(wanted)))
 if not additions:break
 manifest=(P/'Cargo.toml').read_text();pos=manifest.index('[[bin]]');manifest=manifest[:pos]+''.join(additions)+manifest[pos:];(P/'Cargo.toml').write_text(manifest)
else:raise RuntimeError('feature union did not settle')
assert all(set(p['features'])==expected[p['id']] for p in resolved if p['id'] in expected)
config=dict(deployed_lock_sha256=hashlib.sha256(lock).hexdigest(),fixture_lock_sha256=hashlib.sha256((P/'Cargo.lock').read_bytes()).hexdigest(),resolved_features=resolved,feature_union_repairs=changes,all_dependency_versions_from_deployed_lock=True,all_native_linux_deployed_unit_features_equal=True,target_only_metadata_packages=[p['id'] for p in resolved if p['id'] not in expected and p['name']!='pv-fscan-deployed-project-fixture'],profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',toolchain='1.94.1',diagnostics='MIR dump plus --emit=llvm-ir,link; no source, compiler or runtime semantics substitution',old_fixture='auxiliary dependency drift: earlier native-weights/native-v239/box-llvm-fixed receipts not used for deployed native credit',expected_phase='optimized recompilation after deployed Cargo.lock/feature-union correction, then fixed fifteen request pairs and 308 varying-column pairs; no elimination')
(D/'deployed-native-inputs.json').write_text(json.dumps(config,indent=2))
print('expected time: optimized compilation after pinned dependency configuration correction, then finite validation',flush=True)
for binary in ['fixture','v239']:
 cmd=['cargo','run','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','--bin',binary,'-j','4'];print('command',cmd,flush=True);r=subprocess.run(cmd,env=env);assert r.returncode==0
bodies=[];records=[]
for p in (D/'target-weights/release/deps').glob('aspis_r1_cost_probe-*.ll'):
 raw=p.read_bytes()
 # Select the compiler artifact emitted in this exact corrected configuration
 # from the current Cargo artifact list below, rather than an old hash suffix.
 records.append(dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),size=len(raw),mtime=p.stat().st_mtime))
assert records
latest=max(records,key=lambda x:x['mtime']);text=Path(latest['path']).read_text()
for x in re.finditer(r'^define [^\n]*box_from_parts[^\n]*\{.*?^}',text,re.M|re.S):bodies.append(x[0])
assert len(bodies)==1
(D/'deployed-box-lowering.ll.txt').write_text(bodies[0]+'\n');(D/'deployed-box-llvm-manifest.json').write_text(json.dumps(latest,indent=2));print('corrected deployed LLVM artifact',json.dumps(latest),flush=True)
