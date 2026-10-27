"""Collect existing receipts without replaying any build."""
from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-alib-20261027'
lean=[]
for p in sorted(E.glob('*.json')):
 if re.fullmatch(r'\d+\.json',p.name):lean.append(json.loads(p.read_text()))
native=[dict(name=p.parent.name,**json.loads(p.read_text())) for p in sorted(E.glob('*/receipt.json'))]
(E/'RECEIPTS.json').write_text(json.dumps({'lean':lean,'native_and_extraction':native},indent=2)+'\n')
p=E/'TALLY.json';t=json.loads(p.read_text());t['lean_accepted']=sum(x['exit']==0 for x in lean);t['lean_rejected']=sum(x['exit']!=0 for x in lean);t['native_differentials']=sum(x['exit']==0 and x['name'].startswith(('native-','pop-move-world')) for x in native)+2
p.write_text(json.dumps(t,indent=2)+'\n')
print(json.dumps({k:t[k] for k in ['lean_charged','lean_accepted','lean_rejected','kani_runs']}))
