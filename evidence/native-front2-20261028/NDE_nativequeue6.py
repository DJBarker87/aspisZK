from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for n,t,cfg in [(33,'NDE_empty_root',''),(34,'NDE_empty_root','NDE_invert'),(35,'NDE_carry_step','NDE_carry_step'),(36,'NDE_carry_step','NDE_carry_step --cfg NDE_invert')]:
 env=dict(os.environ)
 if cfg:env['NDE_RUST_CFG']=cfg
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_K{n:03}','kani','pool_v1::pair_forest_semantic_terminal::NDE_native::'+t],env=env)
 if r.returncode:raise SystemExit(r.returncode)
