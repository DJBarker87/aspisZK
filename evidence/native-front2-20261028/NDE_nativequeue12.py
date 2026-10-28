from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for n,t,mode in [(75,'pool_v1::pair_forest_terminal::NDE_terminal::NDE_semantic_view','NDE_view'),(77,'pool_v1::pair_forest_copy_terminal::NDE_native::NDE_residual_domain','NDE_residual'),(79,'pool_v1::pair_forest_semantic_terminal::NDE_native::NDE_equality_domain','NDE_eq_step')]:
 for k in range(2):
  cfg=mode+(' --cfg '+('NDE_view_invert' if n==75 else 'NDE_domain_invert') if k else '')
  r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_K{n+k:03}','kani',t],env=dict(os.environ,NDE_RUST_CFG=cfg))
  if r.returncode:raise SystemExit(r.returncode)
