from pathlib import Path
import os,subprocess,json
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027/dropfree');rows=[]
for op in [205,212,215,216,219]:
 env=dict(os.environ,VARIANT='03',PREPARE_ONLY='1');subprocess.run(['python3',str(D/'run_combined.py'),str(op)],env=env,check=True)
 for row in json.loads((D/f'phase-input-{op}-03'/'phases.json').read_text()):row['key']=f'{op}-03';row['phase']='charon' if Path(row['directory']).name.startswith('charon') else 'aeneas';rows.append(row)
N=D/'native';rows.append(dict(key='native',phase='native',directory=str(D/'native-checks-02'),cwd=str(N),revision=(D/'revision').read_text().strip(),print_axioms='N/A finite SHA checks after source change',target=['timeout','180','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract','CARGO_TARGET_DIR='+str(D.parent/'charon-target'),'cargo','test','--release','--offline','--manifest-path',str(N/'Cargo.toml'),'--lib','--jobs','4','sha_checks::']))
P=D/'batch-missing-03';P.mkdir();(P/'phases.json').write_text(json.dumps(rows,indent=2))
