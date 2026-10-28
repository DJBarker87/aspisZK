"""Compilation is the expected cost; execution is a small finite range check."""
from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(D/'range-source.py')],check=True)
rustc='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc'
command=[rustc,'--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no',str(D/'range-native.rs'),'-o',str(D/'range-native')]
subprocess.run(command,check=True)
result=subprocess.run([str(D/'range-native')],check=True,text=True,capture_output=True)
print(result.stdout)
(D/'range-native-result.json').write_text(json.dumps(dict(command=command,rustc_version=subprocess.check_output([rustc,'-vV'],text=True),source_sha256=sha(D/'range-native.rs'),binary_sha256=sha(D/'range-native'),result=result.stdout,evidence_class='finite library validation; not a complete V260 row',configuration='1.94.1 optimized release profile; core usize methods have no feature-conditioned bodies; no Cargo dependencies or artifact feature graph claimed by this standalone library test'),indent=2)+'\n')
