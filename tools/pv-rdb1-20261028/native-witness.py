from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028');O=D/'witness-config';O.mkdir(exist_ok=True)
rustc='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc'
cmd=[rustc,'--edition=2021','-Copt-level=3','-Cdebug-assertions=false','-Coverflow-checks=false','-Cpanic=unwind',str(D/'result-effect-witness.rs'),'-o',str(O/'check')]
(O/'configuration.json').write_text(json.dumps(dict(command=cmd,toolchain=subprocess.check_output([rustc,'-vV'],text=True),source_sha256=hashlib.sha256((D/'result-effect-witness.rs').read_bytes()).hexdigest(),profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',fixture_crates='std/alloc/core only; no feature-bearing project dependency',client_features=dict(path='resolved-features.json',sha256=hashlib.sha256((D/'resolved-features.json').read_bytes()).hexdigest())),indent=2)+'\n')
subprocess.run(cmd,check=True);subprocess.run([str(O/'check')],check=True)
