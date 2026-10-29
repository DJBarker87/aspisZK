"""One optimized deployed-feature MIR/finite-validation scope; no extraction."""
from pathlib import Path
import os,json,subprocess,hashlib,tomllib
D=Path('/home/dombarker/project-offloads/codex-pv-ownb-20261029');P=D/'probe'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target'),CARGO_BUILD_JOBS='4',RUSTC_BOOTSTRAP='1')
meta=json.loads(subprocess.check_output(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--format-version','1','--locked'],env=env,text=True))
nodes={n['id']:n for n in meta['resolve']['nodes']}
expected={}
for u in json.loads((D/'deployed-units.json').read_text()):expected.setdefault(u['package_id'],set()).update(u['features'])
allowed={(x['name'],x['version'])for x in tomllib.loads((D/'deployed-client-Cargo.lock').read_text())['package']}
for p in meta['packages']:
 assert (p['name'],p['version']) in allowed or p['name']=='pv-fscan-deployed-project-fixture'
 if p['id'] in expected:assert set(nodes[p['id']]['features'])==expected[p['id']],p['id']
pins=json.loads((D/'native-inputs.json').read_text())
for x in pins['sources']:
 assert hashlib.sha256(Path(x['host_path']).read_bytes()).hexdigest()==x['sha256'],x
cmd=['cargo','rustc','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','--bin','layout_probe','-j','4','--','--emit=mir,link','-Zprint-type-sizes','-Zdump-mir-dir='+str(D/'mir'),'-Zdump-mir-exclude-pass-number']
print('expected phase: optimized dependency compilation, then MIR emission and finite lifecycle validation',flush=True)
r=subprocess.run(cmd,env=env);assert r.returncode==0
r=subprocess.run([str(D/'target/release/layout_probe')],capture_output=True,text=True);print(r.stdout,r.stderr,flush=True);assert r.returncode==0
files=[]
for p in [*(D/'mir').glob('*.mir'),*(D/'target/release/deps').glob('layout_probe*.mir')]:
 files.append(dict(path=str(p),size=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
j=dict(command=cmd,features=[dict(id=p['id'],features=nodes[p['id']]['features'])for p in meta['packages']],profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',rustc=subprocess.check_output(['rustc','-Vv'],env=env,text=True),stdout=r.stdout,exit=r.returncode,mir=files,finite_validation_only=True,classification='MIR/compiler correspondence is reclassification within existing tool trust; no source-to-world proof')
(D/'native-result.json').write_text(json.dumps(j,indent=2))
print('MIR files',len(files),flush=True)
