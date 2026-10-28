"""Credit caller payload obligations only after both actual caller checks pass."""
from pathlib import Path
import json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin43-20261028'
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
required=['R1Z.PV_RunJoin_CallerDomain43','R1Z.PV_RunJoin_CallerSuccess43']
assert all(m in accepted for m in required),'whole actual caller has not passed'
x=json.loads((R/'evidence/pv-runjoin41-20261028/caller-domain-obligations.json').read_text())
for row in x['rows']:
 row['whole_caller_association']=True
 row['whole_caller_theorem']='R1Z.PV_RunJoin_CallerSuccess43.success'
 row['composition']='R1Z.PV_RunJoin_CallerDomain43.post / R1Z.PV_RunJoin_LayoutPieces43.domain'
x['remaining']='Every listed successful actual-caller Domain obligation is discharged. No endpoint premise or whole ledger row is removed by this source byte-domain result.'
x['accepted_modules']={m:accepted[m]['object_sha256'] for m in required}
(E/'caller-domain-obligations.json').write_text(json.dumps(x,indent=2)+'\n')
print('credited',len(x['rows']),'actual caller record obligations')
