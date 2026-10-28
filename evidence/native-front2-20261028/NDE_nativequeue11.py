from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[]
for n,t in [(65,'NDE_transfer_short'),(67,'NDE_withdrawal_short'),(69,'NDE_request_short')]:
 for k in range(2): jobs.append((n+k,'pool_v1::pair_forest_terminal::NDE_terminal::'+t,'NDE_invert' if k else 'NDE_short'))
for n,t in [(71,'pool_v1::pair_forest_copy_terminal::NDE_native::NDE_binary'),(73,'pool_v1::pair_forest_semantic_terminal::NDE_native::NDE_expected')]:
 for k in range(2):jobs.append((n+k,t,'NDE_simple_invert' if k else 'NDE_simple'))
for n,t,cfg in jobs:
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_K{n:03}','kani',t],env=dict(os.environ,NDE_RUST_CFG=cfg))
 if r.returncode:raise SystemExit(r.returncode)
subprocess.run(['python3',str(E/'NDE_run.py'),'NDE_E012','extract','selected_binary_variant'])
