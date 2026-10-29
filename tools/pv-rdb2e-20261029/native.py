from pathlib import Path
import subprocess,os,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2e-20261029');P=D/'native';old=D.parent/'codex-pv-rdb2c-20261028'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target'),CARGO_BUILD_JOBS='4')
r=subprocess.run(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--format-version','1','--locked'],env=env,capture_output=True,text=True);assert r.returncode==0,r.stderr
meta=json.loads(r.stdout);nodes={p['id']:p for p in meta['resolve']['nodes']};expected={}
for u in json.loads((old/'deployed-units.json').read_text()):expected.setdefault(u['package_id'],set()).update(u['features'])
checks=[]
for p in meta['packages']:
 if p['id'] in expected:checks.append(dict(id=p['id'],features=nodes[p['id']]['features'],expected=sorted(expected[p['id']]),ok=set(nodes[p['id']]['features'])==expected[p['id']]))
assert all(x['ok']for x in checks),[x for x in checks if not x['ok']]
inputs=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in P.glob('*')if p.is_file()]
print('expected time in optimized compilation, then small finite association/dispatch comparisons; no elimination',flush=True)
(D/'native-inputs.json').write_text(json.dumps(dict(inputs=inputs,feature_checks=checks,toolchain=subprocess.check_output(['rustc','-Vv'],env=env,text=True),profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',evidence_class='finite validation only'),indent=2))
subprocess.run(['cargo','run','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','--bin','associations','-j','4'],env=env,check=True)
