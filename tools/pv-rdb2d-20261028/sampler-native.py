from pathlib import Path
import json,subprocess,os,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');P=D/'weights-fixture'
m=(P/'Cargo.toml').read_text()
if 'name="sampler_pairs"' not in m:(P/'Cargo.toml').write_text(m+'\n[[bin]]\nname="sampler_pairs"\npath="sampler-pairs.rs"\n')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target-weights'),CARGO_BUILD_JOBS='4')
r=subprocess.run(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--format-version','1','--locked'],env=env,capture_output=True,text=True);assert r.returncode==0,r.stderr
meta=json.loads(r.stdout);nodes={p['id']:p for p in meta['resolve']['nodes']};expected={}
for u in json.loads((D/'deployed-units.json').read_text()):expected.setdefault(u['package_id'],set()).update(u['features'])
for p in meta['packages']:
 if p['id'] in expected:assert set(nodes[p['id']]['features'])==expected[p['id']],p['id']
records=[]
for p in ['sampler_original.rs','sampler_host.rs','sampler-pairs.rs']:
 b=(P/p).read_bytes();records.append(dict(path=p,sha256=hashlib.sha256(b).hexdigest()))
print('expected time: optimized compilation of finite sampler comparison, then1331 input pairs; no elimination/proof generation',flush=True)
subprocess.run(['cargo','run','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','--bin','sampler_pairs','-j','4'],env=env,check=True)
(D/'rdb2d-sampler-native.json').write_text(json.dumps(dict(sources=records,resolved_features=[dict(id=p['id'],features=nodes[p['id']]['features'])for p in meta['packages']],profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',toolchain=subprocess.check_output(['rustc','-Vv'],env=env,text=True),evidence_class='finite validation only; not a universal source/iterator refinement'),indent=2))
