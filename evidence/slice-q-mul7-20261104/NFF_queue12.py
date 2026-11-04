from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[(74, 'verifier::NFF_incoming::query_prefix_same_inputs', None), (75, 'verifier::NFF_incoming::query_prefix_same_inputs', 'NFF_wrong_query_prefix'), (76, 'verifier::NFF_incoming::query_field_window', None), (77, 'verifier::NFF_incoming::query_field_window', 'NFF_wrong_query_field'), (78, 'verifier::NFF_incoming::query_guard_continuation', None), (79, 'verifier::NFF_incoming::query_guard_continuation', 'NFF_wrong_query_guard'), (80, 'verifier::NFF_incoming::query_geometry_association', None), (81, 'verifier::NFF_incoming::query_geometry_association', 'NFF_wrong_query_geometry'), (82, 'verifier::NFF_incoming::query_node_product_continuation', None), (83, 'verifier::NFF_incoming::query_node_product_continuation', 'NFF_wrong_query_node'), (84, 'verifier::NFF_incoming::opening_address_window', None), (85, 'verifier::NFF_incoming::opening_address_window', 'NFF_wrong_opening_address'), (86, 'verifier::NFF_incoming::query_folded_subslice', None), (87, 'verifier::NFF_incoming::query_folded_subslice', 'NFF_wrong_folded_subslice'), (88, 'verifier::NFF_incoming::query_child_input_frame', None), (89, 'verifier::NFF_incoming::query_child_input_frame', 'NFF_wrong_query_frame'), (90, 'verifier::NFF_incoming::query_slot_partition', None), (6, 'verifier::NFF_incoming::query_slot_partition', 'NFF_wrong_partition'), (9, 'NFF_copy::KMX_checks::KMX_ptr_correct', None), (10, 'NFF_copy::KMX_checks::KMX_ptr_wrong', None)]
for i,h,cfg in jobs:
 a=f'NFF_K{i:03}';env={**os.environ,'NFF_KANI_PAYLOAD':'NFF_INCOMING_PAYLOAD.json','NFF_KANI_BASE':'NFF_INCOMING_BASE.json'}
 if cfg:env['NFF_RUST_CFG']=cfg
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFF_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if cfg or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 if expected and 'VERIFICATION:- FAILED' not in (E/a/'stdout.log').read_text():sys.exit(2)
