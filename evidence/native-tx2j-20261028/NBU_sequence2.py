from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
pairs=[('decode',n) for n in ['exact32','exact8','decode_window','decode_prefix','after_header','live_header']]+[('more',n) for n in ['asf8_header','asf8_ranges','projection','late_header_gate','fill_iteration','frontier_iterator_step','parts','late_length_index','late_ranges','first_byte_cut','lane_control','late_results','encoder_control']]+[('more',f'rows_{family}_{side}') for family in ['after','live'] for side in ['inside','before','after']]+[('more','result_control')]+[('codecs',n) for n in ['after_00','live_00']]
count=5
for mod,name in pairs:
 timedout=False
 for neg in ['', '_negative']:
  if timedout:continue
  count+=1;a=f'NBU_K{count:03}';parent='pair_terminal' if mod in ['decode','codecs'] else 'pair_forest_terminal'
  if count>49:raise SystemExit('Kani stage limit 49; one final independent gate reserved')
  if (E/a/'receipt.json').exists():continue
  harness=f'pool_v1::{parent}::NBU_{mod}::NBU_{name}{neg}'
  r=subprocess.run(['python3',str(E/'NBU_native.py'),'run',a,harness])
  if not (E/a/'receipt.json').exists():raise SystemExit('STOP missing receipt '+a)
  rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
  if neg and rc['exit_status']==0:raise SystemExit('STOP negative passed '+a)
  if 'error[' in log or 'could not compile' in log:raise SystemExit('STOP own source compile error '+a)
  timedout='timed out' in log or rc['exit_status'] in [124,137]
  print('SEQUENCE',a,name+neg,r.returncode,'TIMEOUT' if timedout else '',flush=True)
print('sequence complete',count)
