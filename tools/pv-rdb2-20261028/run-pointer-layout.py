"""Tiny optimized deployed-core layout/read/fold fixture; no arithmetic gate."""
from pathlib import Path
import json,subprocess,os,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028');P=D/'pointer-layout';P.mkdir(exist_ok=True)
src=D/'pointer-layout.rs'
(P/'main.rs').write_bytes(src.read_bytes())
(P/'Cargo.toml').write_text('''[package]
name="pv-rdb2-pointer-layout"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
aspis-core={path="/home/dombarker/project-offloads/codex-pv-fscan-20261028/src/crates/aspis-core",features=["ct-host-prover","r0"]}
[[bin]]
name="pointer-layout"
path="main.rs"
[profile.release]
debug-assertions=false
overflow-checks=false
''')
env=dict(os.environ,RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'pointer-layout-target'),CARGO_BUILD_JOBS='4',PATH='/home/dombarker/.cargo/bin:'+os.environ.get('PATH',''))
cargo='/home/dombarker/.cargo/bin/cargo'
subprocess.run([cargo,'generate-lockfile','--offline','--manifest-path',str(P/'Cargo.toml')],env=env,check=True)
raw=subprocess.check_output([cargo,'metadata','--offline','--locked','--format-version=1','--manifest-path',str(P/'Cargo.toml')],env=env)
(P/'metadata.json').write_bytes(raw);j=json.loads(raw);pkgs={p['id']:p for p in j['packages']}
features=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],features=n['features'],id=n['id']) for n in j['resolve']['nodes']]
core=next(x for x in features if x['name']=='aspis-core');assert core['features']==['ct-host-prover','r0']
cmd=[cargo,'run','--release','--offline','--locked','--manifest-path',str(P/'Cargo.toml'),'-j','4']
(P/'inputs.json').write_text(json.dumps(dict(command=cmd,resolved_features=features,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),metadata_sha256=hashlib.sha256(raw).hexdigest(),profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',toolchain='rustc1.94.1',expected_time='optimized compilation of fixture and dependency; 1024 scalar reads/fold; no elimination or proof generation',evidence_class='finite validation of layout/read/storage effects; no universal pointer law'),indent=2)+'\n')
subprocess.run(cmd,env=env,check=True)
