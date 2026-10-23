#!/usr/bin/env python3
"""Build same harness in baseline/candidate snapshots, preserving artifacts."""
from pathlib import Path
import os,subprocess,sys
R=Path(__file__).resolve().parents[2];H=R.parent
label=sys.argv[1];mode=sys.argv[2]
assert mode in ['corpus','allocations','timing']
features='optimized-terminal,ct-host-prover'+(',public-work-trace' if mode=='corpus' else '')
example='prover_rw_differential' if mode=='corpus' else 'prover_rw_gate'
env=dict(os.environ,CT_EXPECTED='Optimized harness compilation only; no proof generation')
if mode=='allocations':env['PROVER_RW_RUSTFLAGS']='--cfg prover_rw_allocation_audit -C link-arg=-Wl,--threads=4'
subprocess.run(['python3',str(R/'tools/ct-kernels-20261022/refresh-project-mtimes.py'),str(R)],check=True)
runner=R/'tools/prover-rw-20261023/run-host.py'
subprocess.run(['python3',str(runner),label+'-build','cargo','build','--release','-p','aspis-r1-cost-probe','--example',example,'--features',features,'-j','4','--locked'],env=env,check=True)
bin=H/'native-artifacts'/label
assert not bin.exists();bin.write_bytes((H/'target/release/examples'/example).read_bytes());bin.chmod(0o755)
