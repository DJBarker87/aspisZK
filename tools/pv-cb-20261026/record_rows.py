"""Update this worker's source-law table from checked receipts, retaining prior evidence."""
import json,sys
from pathlib import Path
p=Path(__file__).resolve().parents[2]/'evidence/pv-cb-20261026'
a=json.loads((p/'RESUME-SOURCE-ROWS.json').read_text())
rowmap={int(x['op']):x['row'] for x in json.loads((p/'worklist.json').read_text())}
for word in sys.argv[1:]:
 n,attempt=map(int,word.split(':'));r=json.loads((p/f'{attempt}.json').read_text())
 assert r['exit']==0 and any(f'op{n}_source' in x for x in r['axioms'])
 x=dict(op=n,row=rowmap[n],status='ROW-DISCHARGED(candidate)',theorem=f'R1Z.PV_CB_Op{n}Source.op{n}_source',receipt=f'{attempt}.json',note='Exact extracted source function equation, all Result cases retained. D188 extraction trust. No V165/V167 native composition obligation charged to this pure row.')
 a=[y for y in a if y['op']!=n]+[x]
a.sort(key=lambda x:x['op']);count=sum(x['status']=='ROW-DISCHARGED(candidate)' for x in a)
(p/'RESUME-SOURCE-ROWS.json').write_text(json.dumps(a,indent=2)+'\n')
(p/'RESUME-SOURCE-ROWS.md').write_text(f'# Source equation resume\n\nBefore: 0/73 discharged; current: {count}/73. No endpoint removal claimed.\n\n|op|row|status|theorem|receipt / obstruction|\n|---:|---|---|---|---|\n'+''.join(f"|{x['op']}|{x['row']}|{x['status']}|{x['theorem'] or '—'}|{x['receipt']}; {x['note']}|\n" for x in a))
print(f'{count}/73 source rows discharged')
