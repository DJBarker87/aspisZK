from pathlib import Path
import subprocess,os
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');C=H/'src/tools/r1-cost-probe'
e=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/'native-target'),RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4')
subprocess.run(['cargo','+1.94.1','build','--profile','client','--locked','--offline','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','user_fixture_inputs'],cwd=C,env=e,check=True)
r=subprocess.run([H/'native-target/client/user_fixture_inputs'],capture_output=True,check=True)
# Public fixture-only record. Never export actual user witness material.
(H/'fixture-inputs.json').write_bytes(r.stdout)
