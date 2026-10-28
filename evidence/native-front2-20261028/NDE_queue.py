from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(2,'pool_v1::pair_forest_semantic_terminal::NDE_native::NDE_contract',False),(3,'pool_v1::pair_forest_semantic_terminal::NDE_native::NDE_contract',True),(4,'pool_v1::pair_forest_copy_terminal::NDE_native::NDE_contract',False),(5,'pool_v1::pair_forest_copy_terminal::NDE_native::NDE_contract',True),(6,'state_only_poseidon::NDE_native::NDE_contract',False),(7,'state_only_poseidon::NDE_native::NDE_contract',True),(8,'NDE_kmx::KMX_checks::KMX_ptr_correct',False),(9,'NDE_kmx::KMX_checks::KMX_ptr_wrong',False)]
for n,t,neg in jobs:
 env=dict(os.environ)
 if neg:env['NDE_RUST_CFG']='NDE_invert'
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_K{n:03}','kani',t],env=env)
 if r.returncode:raise SystemExit(r.returncode)
