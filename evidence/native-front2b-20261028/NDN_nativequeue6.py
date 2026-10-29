from pathlib import Path
import subprocess,os,json
from NDN_verdicts import classify
E=Path(__file__).resolve().parent
jobs=[(55, 'pool_v1::pair_forest_copy_terminal::NDN_native::tag_geometry_window', 'NDN_tag_geometry'), (56, 'pool_v1::pair_forest_copy_terminal::NDN_native::tag_geometry_window', 'NDN_tag_geometry --cfg NDN_invert'), (57, 'pool_v1::pair_forest_copy_terminal::NDN_native::tag_factors_window', 'NDN_tag_factors'), (58, 'pool_v1::pair_forest_copy_terminal::NDN_native::tag_factors_window', 'NDN_tag_factors --cfg NDN_invert'), (59, 'pool_v1::pair_forest_copy_terminal::NDN_native::tag_accumulate_window', 'NDN_tag_accumulate'), (60, 'pool_v1::pair_forest_copy_terminal::NDN_native::tag_accumulate_window', 'NDN_tag_accumulate --cfg NDN_invert'), (61, 'pool_v1::pair_forest_copy_terminal::NDN_native::tag_reduce_window', 'NDN_tag_reduce'), (62, 'pool_v1::pair_forest_copy_terminal::NDN_native::tag_reduce_window', 'NDN_tag_reduce --cfg NDN_invert')]
for n,t,cfg in jobs:
 r=subprocess.run(['python3',str(E/'NDN_run.py'),f'NDN_K{n:03}','kani',t],env=dict(os.environ,NDN_RUST_CFG=cfg),stdout=(E/f'NDN_K{n:03}-console.log').open('w'),stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NDN_K{n:03}/stdout.log').read_text()
 expected='CHECK_FAILURE' if ('NDN_invert' in cfg or 'NDN_old_header_ref' in cfg or t.endswith('header_copy_negative')) else 'PASS'
 actual=classify(log)
 if actual!=expected:
  print('STOP unexpected native result',n,actual,'expected',expected,flush=True);break
 print('finished',n,flush=True)
