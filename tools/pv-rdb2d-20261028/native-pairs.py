from pathlib import Path
import os,json,subprocess,hashlib,tomllib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');P=D/'weights-fixture'
m=(P/'Cargo.toml').read_text();suffix='\n[[bin]]\nname="forest"\npath="forest.rs"\n'
if 'name="forest"' not in m:(P/'Cargo.toml').write_text(m+suffix)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target-weights'),CARGO_BUILD_JOBS='4')
r=subprocess.run(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--format-version','1','--locked'],env=env,capture_output=True,text=True);assert r.returncode==0,r.stderr
meta=json.loads(r.stdout);nodes={x['id']:x for x in meta['resolve']['nodes']};expected={}
for u in json.loads((D/'deployed-units.json').read_text()):expected.setdefault(u['package_id'],set()).update(u['features'])
lock=tomllib.loads((D/'deployed-client-Cargo.lock').read_text());allowed={(x['name'],x['version']) for x in lock['package']}
for p in meta['packages']:
 assert (p['name'],p['version']) in allowed or p['name']=='pv-fscan-deployed-project-fixture'
 if p['id'] in expected:assert set(nodes[p['id']]['features'])==expected[p['id']],p['id']
print('expected time: optimized dependency recompilation (prior target removed), then three closed row/mask executions with allocator event logging and actual null-handler aborts',flush=True)
subprocess.run(['cargo','build','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','--bin','forest','-j','4'],env=env,check=True)
rows=[]
for mode in ['rows','owned','mask']:
 for fail in [0,1,2,3]:
  r=subprocess.run([str(D/'target-weights/release/forest'),str(fail),mode],capture_output=True,text=True)
  rows.append(dict(mode=mode,fail_at=fail,exit=r.returncode,stdout=r.stdout,stderr=r.stderr));print(json.dumps(rows[-1]),flush=True)
(D/'rdb2d-forest-pairs.json').write_text(json.dumps(dict(checks=rows,resolved_features=[dict(id=p['id'],features=nodes[p['id']]['features'])for p in meta['packages']],profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',rustc=subprocess.check_output(['rustc','-Vv'],env=env,text=True),finite_validation_only=True),indent=2))
assert all(r['exit']==(0 if r['fail_at']==0 else -6) for r in rows)
