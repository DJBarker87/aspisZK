from pathlib import Path
import os,subprocess,json
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027/dropfree');rows=[]
for op,suffix,source,body in [(36,'03','36-generic-ownership.rs',True),(36,'04','36.rs',False),*[(n,'02',f'{n}.rs',False) for n in [205,212,215,216,219]]]:
 env=dict(os.environ,VARIANT=suffix,PROBE_SOURCE=source,PREPARE_ONLY='1',VEC_BODY='1' if body else '0');subprocess.run(['python3',str(D/'run_combined.py'),str(op)],env=env,check=True)
 for row in json.loads((D/f'phase-input-{op}-{suffix}'/'phases.json').read_text()):row['key']=f'{op}-{suffix}';row['phase']='charon' if Path(row['directory']).name.startswith('charon') else 'aeneas';rows.append(row)
N=D/'native';(N/'Cargo.toml').write_text((D/'packages/252-05/Cargo.toml').read_text().replace('pv-r2-dropfree','pv-r2-dropfree-checks'))
rows.append(dict(key='native',phase='native',directory=str(D/'native-checks-01'),cwd=str(N),revision=(D/'revision').read_text().strip(),print_axioms='N/A native finite checks',target=['timeout','180','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract','CARGO_TARGET_DIR='+str(D.parent/'charon-target'),'cargo','test','--release','--offline','--manifest-path',str(N/'Cargo.toml'),'--lib','--jobs','4']))
P=D/'batch-missing-02';P.mkdir();(P/'phases.json').write_text(json.dumps(rows,indent=2))
