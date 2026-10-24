from pathlib import Path
import os,subprocess,sys
D=Path(__file__).resolve().parent
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
kind=sys.argv[1];assert kind in ['escape','capture']
manifest=D/'fixtures/Cargo.toml'
if kind=='escape':
 subprocess.run(['cargo','test','--manifest-path',str(manifest),'--offline','--release','--jobs','4'],check=True)
charon=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--precise-drops','--start-from','crate::'+('escape' if kind=='escape' else 'captured'),'--start-from','crate::captured','--dest-file',str(H/'native-drop'/('ProverRwNativeDrop'+kind+'.llbc')),'--','--manifest-path',str(manifest),'--offline','--release','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd).returncode)
