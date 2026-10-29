from pathlib import Path
import subprocess,os,json
from NDN_verdicts import classify
E=Path(__file__).resolve().parent
jobs=[(47, 'pool_v1::pair_forest_copy_terminal::NDN_native::pattern_route_window', 'NDN_pattern_route'), (48, 'pool_v1::pair_forest_copy_terminal::NDN_native::pattern_route_window', 'NDN_pattern_route --cfg NDN_invert'), (49, 'pool_v1::pair_forest_copy_terminal::NDN_native::pattern_write_window', 'NDN_pattern_write'), (50, 'pool_v1::pair_forest_copy_terminal::NDN_native::pattern_write_window', 'NDN_pattern_write --cfg NDN_invert'), (51, 'pool_v1::pair_forest_semantic_terminal::NDN_native::equality_factor_window', 'NDN_eq_factor'), (52, 'pool_v1::pair_forest_semantic_terminal::NDN_native::equality_factor_window', 'NDN_eq_factor --cfg NDN_invert'), (53, 'pool_v1::pair_forest_semantic_terminal::NDN_native::equality_outer_window', 'NDN_eq_outer'), (54, 'pool_v1::pair_forest_semantic_terminal::NDN_native::equality_outer_window', 'NDN_eq_outer --cfg NDN_invert')]
for n,t,cfg in jobs:
 r=subprocess.run(['python3',str(E/'NDN_run.py'),f'NDN_K{n:03}','kani',t],env=dict(os.environ,NDN_RUST_CFG=cfg),stdout=(E/f'NDN_K{n:03}-console.log').open('w'),stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NDN_K{n:03}/stdout.log').read_text()
 expected='CHECK_FAILURE' if ('NDN_invert' in cfg or 'NDN_old_header_ref' in cfg or t.endswith('header_copy_negative')) else 'PASS'
 actual=classify(log)
 if actual!=expected:
  print('STOP unexpected native result',n,actual,'expected',expected,flush=True);break
 print('finished',n,flush=True)
