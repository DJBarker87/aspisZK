"""Optimized reference test then independently associated Charon extraction."""
from pathlib import Path
import json,subprocess
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
D=Path(__file__).resolve().parent
C='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
commands=[['/home/dombarker/.cargo/bin/cargo','test','--release','--offline','--manifest-path',str(D/'printer-probe/Cargo.toml'),'--jobs','4'],
          [C,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--precise-drops','--start-from','crate::counter_probe','--dest-file',str(H/'native-drop-abi/ProverRwNativeDropABIPrinter.llbc'),'--','--manifest-path',str(D/'printer-probe/Cargo.toml'),'--offline','--release','--lib','--jobs','4']]
print(json.dumps({'expected_phase':'tiny optimized Rust reference compilation/test, then Charon extraction; no arithmetic aggregation','child_commands':commands}),flush=True)
for cmd in commands: subprocess.run(cmd,cwd=D/'printer-probe',check=True)
