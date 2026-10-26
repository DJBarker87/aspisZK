"""Extract the current release selected-mask owner, not the old checked copy."""
from pathlib import Path
import os,subprocess
r=Path(__file__).resolve().parents[3]
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','aspis_core','--start-from','crate::mask','--include','aspis_core::state_only_hiding','--include','aspis_core::field','--dest-file',str(r/'ProverRwP7Mask.llbc'),'--','--manifest-path',str(r/'tools/prover-rw-20261023/success-p7/proof/Cargo.toml'),'--offline','--release','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
