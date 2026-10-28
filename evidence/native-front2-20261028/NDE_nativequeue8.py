from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for n,t in [(46,'NDE_stub_log'),(48,'NDE_row')]:
 for neg in range(2):
  env=dict(os.environ)
  if neg:env['NDE_RUST_CFG']='NDE_invert'
  r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_K{n+neg:03}','kani','pool_v1::pair_forest_copy_terminal::NDE_native::'+t],env=env)
  if r.returncode:raise SystemExit(r.returncode)
