from pathlib import Path
import os,subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028');O=D/'v181-native-config';O.mkdir(exist_ok=True)
rustc='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc'
cmd=[rustc,'--edition=2021','-Copt-level=3','-Cdebug-assertions=false','-Coverflow-checks=false','-Cpanic=unwind',str(D/'v181-native.rs'),'-o',str(D/'v181-native-config/check')]
(O/'configuration.json').write_text(json.dumps(dict(toolchain=subprocess.check_output([rustc,'-vV'],text=True),command=cmd,profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',input_pins={f:hashlib.sha256((D/f).read_bytes()).hexdigest() for f in ['v181-native.rs','capacity-reference.rs']},fixture_crates='std/alloc/core only; no project feature-bearing crate linked',resolved_client_features=dict(path='resolved-features.json',sha256=hashlib.sha256((D/'resolved-features.json').read_bytes()).hexdigest()),evidence_class='finite native validation; not universal proof',expected_time='optimized std-only compilation then1027 finite capacity/error pairs'),indent=2)+'\n')
subprocess.run(cmd,check=True);subprocess.run([str(O/'check')],check=True)
