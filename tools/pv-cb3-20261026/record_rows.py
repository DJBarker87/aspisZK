"""Credit callback source laws only after a successful checked theorem receipt."""
from pathlib import Path
import json,sys
root=Path(__file__).resolve().parents[2];p=root/'evidence/pv-cb3-20261026'
rows=json.loads((p/'worklist.json').read_text())
for arg in sys.argv[1:]:
 op,attempt=map(int,arg.split(':'));receipt=json.loads((p/f'{attempt}.json').read_text())
 assert receipt['exit']==0 and any(f'op{op}_source' in s for s in receipt['axioms'])
 for x in rows:
  if x['op']==op:
   x.update(status='ROW-DISCHARGED(candidate)',theorem=f'R1Z.PV_CB3_Op{op}Source.op{op}_source',receipt=f'{attempt}.json',note='Complete extracted Result equation for arbitrary inputs; no desired-output premise. D188 extraction trust retained; pure callback closure does not require native composition V165–V167.')
(p/'worklist.json').write_text(json.dumps(rows,indent=2)+'\n')
count=sum(x['status']=='ROW-DISCHARGED(candidate)' for x in rows)
(p/'ROWS.md').write_text(f'''# Callback source-law worklist

Recount-2 baseline → baseline plus this worker: OPEN 110 → {110-count};
independent OPEN 51 → {51-count}; CLOSED-ON-CANDIDATE 40 → {40+count}.
Other live sibling changes are not folded into these arithmetic counts.
This worker: {count} ROW-DISCHARGED(candidate). Endpoint premises removed: 0.
No implementation or release pin changed. Target not yet established.

|op|row|status|theorem|receipt|
|---:|---|---|---|---|
'''+''.join(f"|{x['op']}|{x['row']}|{x['status']}|{x.get('theorem','—')}|{x.get('receipt','—')}|\n" for x in rows))
lean=[json.loads(x.read_text()) for x in p.glob('24[789][0-9][0-9].json')]
(p/'budget.json').write_text(json.dumps(dict(lean_compiles=len(lean),lean_passes=sum(x['exit']==0 for x in lean),lean_remaining=100-len(lean),kani_runs=sum(1 for x in p.glob('kani-*/collected-receipt.json') if json.loads(x.read_text()).get('attempt_charged')),kani_remaining=20-sum(1 for x in p.glob('kani-*/collected-receipt.json') if json.loads(x.read_text()).get('attempt_charged'))),indent=2)+'\n')
print(count,'rows credited;',len(lean),'Lean compiles')
