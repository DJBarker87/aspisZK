"""Candidate CU extrema plus inherited geometry/duplicate/PDA targets."""
import json,sys,subprocess,collections
from pathlib import Path
H=Path(sys.argv[1]);O=H.parent/'codex-cx-cu-bound4-20261020'
picks=subprocess.check_output([sys.executable,str(H/'harness/pick_traces.py'),str(H/'sweep/variants/sweep.jsonl'),str(H/'sweep/variants-extra/sweep.jsonl')],text=True).split()
old=json.loads((O/'plan-trace-main.json').read_text())
# The final 16 bound4 selections exercise query geometry, duplicate runs,
# fallback scans, and expensive positions beyond the per-variant CU extrema.
picks+= [r['source'] for r in old['runs'][48:]]
# Include the measured maximum across the complete accepted sweep, even
# when it is above the grid's own maximum. This does not add variant maxima.
groups=collections.defaultdict(list)
for ss in ['control','variants','variants-extra','targeted','random-a','random-b']:
 for line in (H/f'sweep/{ss}/sweep.jsonl').read_text().splitlines():
  row=json.loads(line);i=row['inputs'];mode='genesis' if i['zeroed_genesis_page'] else row['history_mode']
  groups[('settlement_cu',row['kind'],i['split'],mode,bool(i['prefund_marker_lamports']))].append((ss,row))
  groups[('stage1_cu',row['kind'],i['split'])].append((ss,row))
for group,rs in groups.items():
 ss,row=max(rs,key=lambda x:x[1][group[0]])
 picks.append(ss+':'+row['label'])
picks=list(dict.fromkeys(picks));(H/'trace-picks.txt').write_text(' '.join(picks)+'\n')
subprocess.run([sys.executable,str(H/'harness/make_trace_plan.py'),str(H),'trace-main',*picks],check=True)
subprocess.run([sys.executable,str(H/'harness/trace_controls.py'),str(H)],check=True)
