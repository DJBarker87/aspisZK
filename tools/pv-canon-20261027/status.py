from pathlib import Path
import json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-canon-20261027';t=json.loads((E/'tally.json').read_text());rows=[]
for p in sorted((R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_Canon_*.lean')):
 receipts=[json.loads(q.read_text()) for q in E.glob('44*/receipt.json') if json.loads(q.read_text()).get('target')=='R1Z/'+p.stem]
 last=max(receipts,key=lambda q:q['attempt']) if receipts else None
 rows.append(dict(module=p.stem,status=('passed' if last['exit']==0 else 'failed draft') if last else 'uncompiled draft',attempt=last['attempt'] if last else None))
(E/'STATUS.json').write_text(json.dumps(dict(budget=t,modules=rows,privacy_target='not yet established',V403='OPEN pending installed association and full caller trace binding'),indent=2)+'\n')
print('Lean',t['lean'],'Kani',t['kani'],'passed',sum(r['status']=='passed' for r in rows),'draft',sum(r['status']!='passed' for r in rows))
