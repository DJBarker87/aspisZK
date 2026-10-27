"""Focused source222 loop checks; stop on any failure/refusal, never overlap scopes."""
from pathlib import Path
import subprocess,json,sys
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
for m in ['PV_B3_Result','PV_B3_BoundedLoop','PV_B3_PrefixCounter222','PV_B3_PrefixRank222','PV_B3_PrefixFinite222','PV_B3_EvalCounter222','PV_B3_EvalRank222','PV_B3_EvalFinite222']:
 t=json.loads((H/'TALLY-batch3b.json').read_text())
 if t['lean_attempts']>=40:sys.exit('extraction stage40-attempt ceiling reached')
 if (H/'lean-objects'/(m+'.olean')).exists():
  print('REUSE',m,flush=True);continue
 r=subprocess.run(['python3',str(H/'compile_batch3b.py'),m])
 if r.returncode:sys.exit(r.returncode)
