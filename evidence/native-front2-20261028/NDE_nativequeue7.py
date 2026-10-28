from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for n,t,cfg in [(42,'NDE_sum_step','NDE_sum_step'),(43,'NDE_sum_step','NDE_sum_step --cfg NDE_invert'),(44,'NDE_reconstruct_step','NDE_reconstruct_step'),(45,'NDE_reconstruct_step','NDE_reconstruct_step --cfg NDE_invert')]:
 env=dict(os.environ,NDE_RUST_CFG=cfg)
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_K{n:03}','kani','pool_v1::pair_forest_semantic_terminal::NDE_native::'+t],env=env)
 if r.returncode:raise SystemExit(r.returncode)
