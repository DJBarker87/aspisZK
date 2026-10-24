from pathlib import Path
import os,subprocess
D=Path(__file__).resolve().parent;R=D.parents[2]
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--precise-drops','--start-from','crate::real_drop','--start-from','crate::live_borrow','--include','getrandom::error::Error','--include','core::num::nonzero::NonZero','--include','core::num::niche_types::NonZeroI32Inner','--dest-file',str(D/'ProverRwRngExtractordrop010.llbc'),'--','--manifest-path',str(D/'drop-probe/Cargo.toml'),'--offline','--release','--lib','--jobs','4']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_TARGET_DIR=str(R.parent/'rng-charon-target'))
raise SystemExit(subprocess.run(cmd,cwd=R,env=env).returncode)
