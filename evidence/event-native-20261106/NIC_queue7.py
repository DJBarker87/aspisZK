from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
jobs=[(63, 'fold_atom_pure'), (64, 'fold_atom_control'), (65, 'pairing_raw_pure'), (66, 'pairing_raw_control'), (67, 'pairing_fold_pure'), (68, 'pairing_fold_control'), (69, 'accum_tail_pure'), (70, 'accum_tail_control'), (71, 'decoder_pure'), (72, 'decoder_control'), (73, 'q_subtract_pure'), (74, 'q_subtract_control'), (75, 'line_scale_pure'), (76, 'line_scale_control')]
for i,target in jobs:
 a=f'NIC_K{i:03d}'
 p=subprocess.run(['python3',str(E/'NIC_kani_run.py'),a,'kani',target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(p.stdout+p.stderr)
 receipt=E/a/'receipt.json'
 if not receipt.exists():print(a,'PRELAUNCH ERROR',flush=True);break
 r=json.loads(receipt.read_text());print(a,target,r['exit_status'],r['wall_seconds'],flush=True)
 if r['exit_status'] in [124,137] or 'timed out' in (E/a/'stdout.log').read_text().lower():print('review required',flush=True);break
