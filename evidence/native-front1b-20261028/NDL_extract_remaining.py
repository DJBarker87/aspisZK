"""Serial remaining-budget reference extraction; every new output stays OPEN."""
import os,subprocess,json
from pathlib import Path
E=Path(__file__).resolve().parent
roots=['tensor_write_ref','scalar_add_step_ref','high_step_ref','channel_add_ref','block_reduce_ref','cm_square_factors_ref','node_parts_ref','occupied_parts_ref','sibling_parts_ref','binary_parent_index_ref','occupied_domain_ref','root_guard_ref','wellformed_length_ref','box_record_ref','tensor_stage_ref']
rows=[]
for n,root in enumerate(roots,6):
 attempt=f'NDL_E{n:03}';namespace='NDL_Part'+str(n).zfill(2)+'Ref'
 env=dict(os.environ,NDL_EXTRACT_CONFIG=json.dumps(dict(namespace=namespace,roots=[root])))
 if not (E/attempt/'receipt.json').exists():
  r=subprocess.run(['python3',str(E/'NDL_run.py'),attempt,'extract',root],env=env)
  assert r.returncode==0,'runner failure; inspect before continuing'
 rc=json.loads((E/attempt/'receipt.json').read_text())
 row=dict(attempt=attempt,reference=root,namespace=namespace,exit_status=rc['exit_status'],status='OPEN: extraction artifact only; no new Lean/cohort equality or native claim')
 if rc['exit_status']==0:
  r=subprocess.run(['python3',str(E/'NDL_fetch_extraction.py'),namespace]);assert r.returncode==0
 rows.append(row);(E/'NDL_PARTIAL_EXTRACTIONS.json').write_text(json.dumps(rows,indent=2)+'\n')
