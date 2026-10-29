from pathlib import Path
import subprocess,os,json
from NDN_verdicts import classify
E=Path(__file__).resolve().parent
jobs=[(42, 'state_only_poseidon::NDN_native::interpolation_factors', 'NDN_interpolation_factors'), (43, 'state_only_poseidon::NDN_native::interpolation_factors', 'NDN_interpolation_factors --cfg NDN_invert'), (44, 'state_only_poseidon::NDN_native::interpolation_sum', 'NDN_interpolation_sum'), (45, 'state_only_poseidon::NDN_native::interpolation_sum', 'NDN_interpolation_sum --cfg NDN_invert'), (46, 'pool_v1::pair_forest_copy_terminal::NDN_native::pattern_step_window', 'NDN_pattern_step'), (47, 'pool_v1::pair_forest_copy_terminal::NDN_native::pattern_step_window', 'NDN_pattern_step --cfg NDN_invert'), (48, 'pool_v1::pair_forest_semantic_terminal::NDN_native::equality_factor_window', 'NDN_eq_factor'), (49, 'pool_v1::pair_forest_semantic_terminal::NDN_native::equality_factor_window', 'NDN_eq_factor --cfg NDN_invert'), (50, 'pool_v1::pair_forest_semantic_terminal::NDN_native::equality_outer_window', 'NDN_eq_outer'), (51, 'pool_v1::pair_forest_semantic_terminal::NDN_native::equality_outer_window', 'NDN_eq_outer --cfg NDN_invert')]
for n,t,cfg in jobs:
 r=subprocess.run(['python3',str(E/'NDN_run.py'),f'NDN_K{n:03}','kani',t],env=dict(os.environ,NDN_RUST_CFG=cfg),stdout=(E/f'NDN_K{n:03}-console.log').open('w'),stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NDN_K{n:03}/stdout.log').read_text()
 expected='CHECK_FAILURE' if ('NDN_invert' in cfg or 'NDN_old_header_ref' in cfg or t.endswith('header_copy_negative')) else 'PASS'
 actual=classify(log)
 if actual!=expected:
  print('STOP unexpected native result',n,actual,'expected',expected,flush=True);break
 print('finished',n,flush=True)
