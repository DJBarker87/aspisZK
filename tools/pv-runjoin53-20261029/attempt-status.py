from pathlib import Path
import json
E=Path(__file__).resolve().parents[2]/'evidence/pv-runjoin53-20261029'
r=[json.loads(p.read_text()) for p in E.glob('receipt-*.json')]
print('Attempts',len(r),'accepted',sum(x['accepted'] for x in r))
print('Unused non-audit IDs:',[a for a in range(66100,66197) if not (E/f'receipt-{a}.json').exists()])
print('Current rejected modules:',sorted({v['module'] for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if not v['accepted']}-{v['module'] for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}))
