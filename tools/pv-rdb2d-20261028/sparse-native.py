from pathlib import Path
import json,subprocess,os,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');P=D/'weights-fixture'
m=(P/'Cargo.toml').read_text()
if 'name="sparse_native"' not in m:(P/'Cargo.toml').write_text(m+'\n[[bin]]\nname="sparse_native"\npath="sparse-native.rs"\n')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target-weights'),CARGO_BUILD_JOBS='4')
r=subprocess.run(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--format-version','1','--locked'],env=env,capture_output=True,text=True);assert r.returncode==0,r.stderr
meta=json.loads(r.stdout);nodes={p['id']:p for p in meta['resolve']['nodes']};expected={}
for u in json.loads((D/'deployed-units.json').read_text()):expected.setdefault(u['package_id'],set()).update(u['features'])
for p in meta['packages']:
 if p['id'] in expected:assert set(nodes[p['id']]['features'])==expected[p['id']],p['id']
records=[]
for p in ['sparse-native.rs']:
 b=(P/p).read_bytes();records.append(dict(path=p,sha256=hashlib.sha256(b).hexdigest()))
print('expected time: optimized compilation of finite sampler comparison, theneleven public-width allocation traces and two actual OOM prefixes; no elimination/proof generation',flush=True)
subprocess.run(['cargo','build','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','--bin','sparse_native','-j','4'],env=env,check=True)
checks=[]
for width,fail in [(w,0)for w in range(11)]+[(0,1),(10,1)]:
 r=subprocess.run([str(D/'target-weights/release/sparse_native'),str(width),str(fail)],capture_output=True,text=True)
 expected=f"A 1 {24*(1<<width)} 8 0 {int(fail!=0)}\n"
 assert r.stderr.startswith(expected),(width,fail,r.stderr)
 if fail:assert r.returncode==-6 and f"memory allocation of {24*(1<<width)} bytes failed" in r.stderr
 else:assert r.returncode==0 and r.stderr==expected+f"D 2 {24*(1<<width)} 8 0 0\n"
 checks.append(dict(width=width,fail=fail,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))
(D/'rdb2d-sparse-native.json').write_text(json.dumps(dict(checks=checks,sources=records,resolved_features=[dict(id=p['id'],features=nodes[p['id']]['features'])for p in meta['packages']],profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',toolchain=subprocess.check_output(['rustc','-Vv'],env=env,text=True),evidence_class='finite allocation/layout/prefix validation only'),indent=2))
print(json.dumps(checks),flush=True)
