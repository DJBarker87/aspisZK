from pathlib import Path
import subprocess,os
D=Path(__file__).resolve().parent; R=D.parents[2]
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::old_owner','--include','zeroize::Zeroizing','--dest-file',str(D/'ProverRwRngOwner.llbc'),'--','--manifest-path',str(D/'prototype/Cargo.toml'),'--offline','--release','--lib','--jobs','1']
raise SystemExit(subprocess.run(cmd,cwd=R,env=dict(os.environ,CARGO_TARGET_DIR=str(R.parent/'rng-charon-target'))).returncode)
