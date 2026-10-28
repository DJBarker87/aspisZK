from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for n,t,cfg in [(78,'state_only_poseidon::NDE_native::NDE_matrix_cell','NDE_matrix_step'),(79,'state_only_poseidon::NDE_native::NDE_matrix_cell','NDE_matrix_step --cfg NDE_window_invert'),(80,'pool_v1::pair_forest_semantic_terminal::NDE_native::NDE_equality_domain','NDE_eq_step')]:
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_K{n:03}','kani',t],env=dict(os.environ,NDE_RUST_CFG=cfg))
 if r.returncode:raise SystemExit(r.returncode)
