from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for n,t in [(12,'NDE_initial'),(14,'NDE_scalar'),(16,'NDE_variant')]:
 for i in range(2):
  env=dict(os.environ)
  if i:env['NDE_RUST_CFG']='NDE_invert'
  r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_K{n+i:03}','kani','pool_v1::pair_forest_semantic_terminal::NDE_native::'+t],env=env)
  if r.returncode:raise SystemExit(r.returncode)
