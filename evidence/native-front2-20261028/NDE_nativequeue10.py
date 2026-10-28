from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(56,'state_only_poseidon::NDE_native::NDE_matrix_cell','NDE_matrix_step --cfg NDE_window_invert'),(57,'state_only_poseidon::NDE_native::NDE_scan_cell','NDE_scan_step --cfg NDE_window_invert'),(58,'state_only_poseidon::NDE_native::NDE_packed_after','NDE_packed_after --cfg NDE_window_invert')]
for n,t in [(59,'NDE_transfer_short'),(61,'NDE_withdrawal_short'),(63,'NDE_request_short')]:
 for k in range(2): jobs.append((n+k,'pool_v1::pair_forest_terminal::NDE_native::'+t,'NDE_invert' if k else 'NDE_short'))
for n,t,cfg in jobs:
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_K{n:03}','kani',t],env=dict(os.environ,NDE_RUST_CFG=cfg))
 if r.returncode:raise SystemExit(r.returncode)
