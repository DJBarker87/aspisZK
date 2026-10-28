"""Build scratch probe optimized, retaining toolchain, input and artifact pins."""
from pathlib import Path
import subprocess,json,os,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-integ4-20261027');S=D/'scratch/batch1-cost'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(D/'combined/candidate/native-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
v=subprocess.check_output(['rustc','-vV'],env=env,cwd=D/'source',text=True);assert v.startswith('rustc 1.94.1 ');(S/'rustc-vV.txt').write_text(v)
cmd=['taskset','--cpu-list','0-3','cargo','build','--manifest-path',str(S/'Cargo.toml'),'--release','--offline','-j','4']
(S/'build-command.json').write_text(json.dumps(dict(command=cmd,env={k:env[k] for k in ['CARGO_TARGET_DIR','RUSTFLAGS']},expected_time='optimized scratch microbenchmark compilation; no proof generation'),indent=2))
subprocess.run(cmd,env=env,cwd=D/'source',check=True)
b=Path(env['CARGO_TARGET_DIR'])/'release/pv-integ4-batch1-cost';(S/'bin').mkdir();shutil.copy2(b,S/'bin/pv-integ4-batch1-cost')
paths=[S/'Cargo.toml',S/'Cargo.lock',S/'function-cost.rs',S/'pole_original.rs']+[D/'source'/x for x in ['Cargo.lock','crates/aspis-r1-cost-probe/src/ct_pole.rs','crates/aspis-r1-cost-probe/src/prover_helper_sum.rs','crates/aspis-r1-cost-probe/src/prover_powers.rs','crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-statement/src/state_only_semantic.rs']]
(S/'pins.json').write_text(json.dumps(dict(binary=dict(sha256=hashlib.sha256(b.read_bytes()).hexdigest(),bytes=b.stat().st_size),inputs={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}),indent=2))
