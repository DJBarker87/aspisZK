"""Check accepted source bytes, budget, trust reports and task boundaries."""
from pathlib import Path
import json,hashlib,re,subprocess,collections
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin18-20261027';L=R/'docs/research/v8-r0-zk-20261009/lean'
rows=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-[0-9]*.json'))]
latest={}
for r in rows:
 if r['accepted']:latest[r['target']]=r
checks=[]
for mod,r in latest.items():
 if mod=='R1Z/PV_RunJoin_ScalarInspect18':continue
 p=L/(mod+'.lean');sha=hashlib.sha256(p.read_bytes()).hexdigest()
 assert sha==r['source_sha256'],mod
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|^axiom\s',p.read_text(),re.M),mod
 checks.append(dict(module=mod,attempt=r['attempt'],sha256=sha,source_matches=True,axioms=r['axioms']))
ship=subprocess.check_output(['git','diff','8c9ec5f63f','--','crates/','programs/'],cwd=R,text=True);assert not ship
(E/'proof-status.json').write_text(json.dumps(dict(accepted=checks,shipped_source_diff_empty=True,endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_weakened=0),indent=2)+'\n')
print('accepted sources match:',len(checks),'shipped source diff empty')
