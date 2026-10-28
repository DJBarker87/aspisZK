from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for n,t,neg in [(20,'pool_v1::pair_forest_copy_terminal::NDE_native::NDE_link',True),(21,'pool_v1::pair_forest_semantic_terminal::NDE_native::NDE_claim',False),(22,'pool_v1::pair_forest_semantic_terminal::NDE_native::NDE_claim',True)]:
 env=dict(os.environ)
 if neg:env['NDE_RUST_CFG']='NDE_invert'
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_K{n:03}','kani',t],env=env)
 if r.returncode:raise SystemExit(r.returncode)
