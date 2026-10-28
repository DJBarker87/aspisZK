from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
items=[('more','copy32_boundary_negative'),('more','validator_control'),('more','validator_control_negative'),('decode','decode_children'),('decode','decode_children_negative'),('more','late_header_gate'),('more','late_header_gate_negative'),('more','fill_iteration'),('more','fill_iteration_negative'),('more','frontier_iterator_step'),('more','frontier_iterator_step_negative'),('more','late_length_index'),('more','late_length_index_negative'),('more','late_ranges'),('more','late_ranges_negative'),('more','first_byte_cut'),('more','first_byte_cut_negative'),('more','lane_control'),('more','lane_control_negative'),('more','late_results'),('more','late_results_negative'),('more','encoder_control'),('more','encoder_control_negative')]+[('more',f'rows_{family}_{side}{neg}') for family in ['after','live'] for side in ['inside','before','after'] for neg in ['', '_negative']]
for i,(mod,name) in enumerate(items,2):
 a=f'NBU_K{i:03}'
 if (E/a/'receipt.json').exists():continue
 parent='pair_terminal' if mod in ['decode','codecs'] else 'pair_forest_terminal'
 harness=f'pool_v1::{parent}::NBU_{mod}::NBU_{name}'
 r=subprocess.run(['python3',str(E/'NBU_native.py'),'run',a,harness])
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP no receipt '+a)
 rc=json.loads((E/a/'receipt.json').read_text())
 if name.endswith('_negative') and rc['exit_status']==0:raise SystemExit('STOP negative control passed '+a)
 print('SEQUENCE',a,name,r.returncode,flush=True)
