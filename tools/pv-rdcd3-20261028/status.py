"""Summarize actual receipts; proof counts never grant row credit."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd3-20261028';runs=[];accepted=[]
for p in sorted(E.glob('*/receipt.json')):
 j=json.loads(p.read_text());runs.append(dict(path=str(p.relative_to(E)),**j))
 if j.get('module') and j['exit']==0:
  path=R/j['source_path']
  assert hashlib.sha256(path.read_bytes()).hexdigest()==j['source_sha256'],path
  assert not any('sorryAx' in line for line in j['axioms'])
  accepted.append(dict(module=j['module'],receipt=str(p.relative_to(E)),source_sha256=j['source_sha256'],axioms=j['axioms']))
lean=[j for j in runs if j.get('module')];native=[j for j in runs if not j.get('module')]
d=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),lean_attempts=len(lean),lean_pass=sum(j['exit']==0 for j in lean),lean_fail=sum(j['exit']!=0 for j in lean),native_scopes=len(native),kani=0,accepted_modules=accepted,restored_rows=[],endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[],trust='Any Aeneas/Rust semantic agreement remains existing tool trust, never premise removal',remaining_rows=['V260','V265','V217','V220','V237','V236','V197','V233','V201'])
(E/'STATUS.json').write_text(json.dumps(d,indent=2)+'\n')
print(f"Lean {d['lean_attempts']}/100 ({d['lean_pass']} pass, {d['lean_fail']} fail); native {len(native)}/100; no row restored")
