from pathlib import Path
import subprocess,json,hashlib
D=Path(__file__).parent
rust='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc'
cmd=[rust,'--edition=2021','-Copt-level=3','-Cdebug-assertions=false','-Coverflow-checks=false','-Cpanic=abort','-Clink-arg=-Wl,--threads=4',str(D/'PV_O11_kind_native.rs'),'-o',str(D/'PV_O11_kind_native')]
subprocess.run(cmd,check=True)
p=subprocess.run([str(D/'PV_O11_kind_native')],capture_output=True,text=True)
j=dict(command=cmd,toolchain=subprocess.check_output([rust,'-vV'],text=True),binary_sha256=hashlib.sha256((D/'PV_O11_kind_native').read_bytes()).hexdigest(),binary_bytes=(D/'PV_O11_kind_native').stat().st_size,source_sha256=hashlib.sha256((D/'PV_O11_kind_native.rs').read_bytes()).hexdigest(),profile='release opt3 panic=abort debug_assertions=false overflow_checks=false',features='std-only fixture; no project crates linked; no Cargo features; std getter body matches adopted-toolchain rust-src. Does not exercise deployed client entry.',classification='finite validation only; all source mapping and runtime/compiler obligations retained',exit=p.returncode,stdout=p.stdout,stderr=p.stderr)
(D/'PV_O11_native-result.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j));assert p.returncode==0
