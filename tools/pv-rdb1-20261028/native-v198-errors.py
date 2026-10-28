from pathlib import Path
import os,json,subprocess,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028');P=D/'classification-project-fixture';O=D/'v198-errors-config';O.mkdir(exist_ok=True)
source=(D/'v198-errors.rs').read_bytes();(P/'fixture.rs').write_bytes(source)
manifest=(D/'classify-project-bytes/Cargo.toml.txt').read_bytes();(P/'Cargo.toml').write_bytes(manifest)
env=dict(os.environ,RUSTUP_TOOLCHAIN='1.94.1',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(D/'classification-target'),PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'])
meta=subprocess.check_output(['cargo','metadata','--locked','--manifest-path',str(P/'Cargo.toml'),'--format-version','1'],env=env)
m=json.loads(meta);nodes={x['id']:x for x in m['resolve']['nodes']};features=[dict(name=x['name'],version=x['version'],features=nodes[x['id']]['features']) for x in m['packages']]
for pkg,fs in {'aspis-core':['ct-host-prover','r0'],'aspis-r1-cost-probe':['ct-host-prover','default','private-leaf-salts','prover','r1p-check'],'aspis-prover':['ct-host-prover','insecure-spend-fixture','prover','r0'],'aspis-statement':['r0','pool-v1-kernel']}.items():assert next(x['features'] for x in features if x['name']==pkg)==sorted(fs)
cmd=['cargo','run','--locked','--release','--manifest-path',str(P/'Cargo.toml'),'-j','4']
(O/'configuration.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(source).hexdigest(),manifest_sha256=hashlib.sha256(manifest).hexdigest(),toolchain=subprocess.check_output(['rustc','-vV'],env=env,text=True),features_every_crate=features,profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',command=cmd,evidence_class='finite validation; not universal source proof',expected_time='optimized compilation then 125 finite writer status/buffer checks; no elimination'),indent=2)+'\n')
print('Time expected in optimized compilation then 125 finite writer error/effect checks',flush=True)
subprocess.run(cmd,env=env,check=True)
