from pathlib import Path
import subprocess,os,json
from NDN_verdicts import classify
E=Path(__file__).resolve().parent
jobs=[(63, 'pool_v1::pair_forest_semantic_terminal::NDN_native::fields_word_window', 'NDN_fields_window'), (64, 'pool_v1::pair_forest_semantic_terminal::NDN_native::fields_word_window', 'NDN_fields_window --cfg NDN_invert'), (65, 'pool_v1::pair_forest_terminal::NDN_native::transfer_header_error', 'NDN_payment_transfer'), (66, 'pool_v1::pair_forest_terminal::NDN_native::transfer_header_error', 'NDN_payment_transfer --cfg NDN_invert'), (67, 'pool_v1::pair_forest_terminal::NDN_native::withdrawal_header_error', 'NDN_payment_withdrawal'), (68, 'pool_v1::pair_forest_terminal::NDN_native::withdrawal_header_error', 'NDN_payment_withdrawal --cfg NDN_invert'), (69, 'pool_v1::pair_forest_terminal::NDN_native::request_header_window', 'NDN_request_cut --cfg NDN_old_header_ref'), (70, 'pool_v1::pair_forest_terminal::NDN_native::request_header_window', 'NDN_request_cut'), (71, 'pool_v1::pair_forest_terminal::NDN_native::request_header_window', 'NDN_request_cut --cfg NDN_invert'), (72, 'pool_v1::pair_forest_copy_terminal::NDN_native::frozen_link_binary_domain', 'NDN_binary_caller'), (73, 'pool_v1::pair_forest_copy_terminal::NDN_native::frozen_link_binary_domain', 'NDN_binary_caller --cfg NDN_invert'), (74, 'pool_v1::pair_forest_terminal::NDN_native::result_rejection_window', 'NDN_result_compare'), (75, 'pool_v1::pair_forest_terminal::NDN_native::result_rejection_window', 'NDN_result_compare --cfg NDN_invert'), (76, 'pool_v1::pair_forest_semantic_terminal::NDN_native::header_copy_positive', 'NDN_result_header'), (77, 'pool_v1::pair_forest_semantic_terminal::NDN_native::header_copy_negative', 'NDN_result_header'), (78, 'pool_v1::pair_forest_terminal::NDN_native::result_header_window', 'NDN_result_header'), (79, 'pool_v1::pair_forest_terminal::NDN_native::result_header_window', 'NDN_result_header --cfg NDN_invert'), (80, 'pool_v1::pair_forest_terminal::NDN_native::result_field_window', 'NDN_result_field')]
for n,t,cfg in jobs:
 r=subprocess.run(['python3',str(E/'NDN_run.py'),f'NDN_K{n:03}','kani',t],env=dict(os.environ,NDN_RUST_CFG=cfg),stdout=(E/f'NDN_K{n:03}-console.log').open('w'),stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/f'NDN_K{n:03}/stdout.log').read_text()
 expected='CHECK_FAILURE' if ('NDN_invert' in cfg or 'NDN_old_header_ref' in cfg or t.endswith('header_copy_negative')) else 'PASS'
 actual=classify(log)
 if actual!=expected:
  print('STOP unexpected native result',n,actual,'expected',expected,flush=True);break
 print('finished',n,flush=True)
