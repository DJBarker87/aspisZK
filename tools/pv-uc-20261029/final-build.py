"""Small optimized functional preflight, not final acceptance replay."""
from pathlib import Path
import subprocess,os,json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');C=H/'src/tools/r1-cost-probe'
e=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/'native-target'),RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4')
c=['taskset','--cpu-list','0-3','cargo','+1.94.1','build','--profile','client','--locked','--offline','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','user_client','--bin','user_fixture_inputs','--bin','devnet_spend']
subprocess.run(c,cwd=C,env=e,check=True)
for name in ['user_client','devnet_spend','user_fixture_inputs']:
 p=H/'native-target/client'/name
 print(name,hashlib.sha256(p.read_bytes()).hexdigest(),p.stat().st_size,flush=True)

O=H/'final-gates';O.mkdir(exist_ok=True)
features=subprocess.check_output(['cargo','+1.94.1','metadata','--format-version','1','--locked','--offline','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover'],cwd=C,env=e)
(O/'metadata.json').write_bytes(features)
subprocess.run(['python3',str(H/'build-fixtures.py')],check=True)
record=dict(toolchain=subprocess.check_output(['rustc','+1.94.1','-Vv'],env=e,text=True),command=c,environment={k:e[k] for k in ['RUSTFLAGS','CARGO_TARGET_DIR']},binaries={name:dict(path=str(H/'native-target/client'/name),sha256=hashlib.sha256((H/'native-target/client'/name).read_bytes()).hexdigest(),bytes=(H/'native-target/client'/name).stat().st_size) for name in ['user_client','devnet_spend','user_fixture_inputs']})
(O/'build.json').write_text(json.dumps(record,indent=2)+'\n')
