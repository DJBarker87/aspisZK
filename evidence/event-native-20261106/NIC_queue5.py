from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
jobs=[(46, 'box_abort_prefix'), (47, 'box_abort_control'), (48, 'dot_main_pure'), (49, 'dot_main_control'), (50, 'dot_fold_pure'), (51, 'dot_fold_control'), (52, 'basis_pure'), (53, 'basis_control'), (54, 'node_pure'), (55, 'node_control'), (56, 'row_pure'), (57, 'row_control'), (58, 'flush_pure'), (59, 'flush_control'), (60, 'reduction_pure'), (61, 'reduction_control')]
for i,target in jobs:
 a=f'NIC_K{i:03d}'
 p=subprocess.run(['python3',str(E/'NIC_kani_run.py'),a,'kani',target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(p.stdout+p.stderr)
 receipt=E/a/'receipt.json'
 if not receipt.exists():print(a,'PRELAUNCH ERROR',flush=True);break
 r=json.loads(receipt.read_text());print(a,target,r['exit_status'],r['wall_seconds'],flush=True)
 if r['exit_status'] in [124,137] or 'timed out' in (E/a/'stdout.log').read_text().lower():print('review required',flush=True);break
