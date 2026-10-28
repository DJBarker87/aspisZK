"""Exact uncredited leaves; parent timeouts are replaced, never counted as evidence."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent
pairs=json.loads((E/'KNA_PAIRS.json').read_text());by={p['name']:p for p in pairs}
remaining=[]
def body(lo,hi):
 key=f'body_{lo}_{hi}';p=by.get(key)
 if p and p['credit']:return
 mid=(lo+hi)//2
 if p and hi-lo>1 and (f'body_{lo}_{mid}' in by or f'body_{mid}_{hi}' in by):
  body(lo,mid);body(mid,hi)
 else:
  remaining.append(dict(name=key,range=[lo,hi],status='UNRUN' if not p else p['positive']+'/'+p['control'],next_split=[[lo,mid],[mid,hi]] if p and hi-lo>1 else [[lo,hi]],receipts=[] if not p else [p['positive_id'],p['control_id']]))
for w in range(11):body(160*w,min(1736,160*(w+1)))
body(1736,1768)
rows={}
shared=['LPf_K027','LPi_K017','LPi_K018']
for row in shared:rows[row]=dict(remaining=remaining,status='OPEN' if remaining else 'CONFIRMED')
for row,name in [('LPm_K003','selected'),('LPm_K004','append32'),('LPm_K005','append4'),('LPi_K012','append16'),('LPi_K013','append32')]:
 p=by.get(name);splits=[by.get(f'{name}_byte_{lo}_{hi}') for lo,hi in [(0,884),(884,1768)]]
 good=p and p['credit'] or all(x and x['credit'] for x in splits)
 rows[row]=dict(status='CONFIRMED' if good else 'OPEN',domain='i<64; len=712+16*i' if name=='selected' else 'symbolic len<='+str({'append32':1704,'append4':1732,'append16':1720}[name]),gates=[x for x in [p]+splits if x],next='For each uncredited byte interval, halve the observation interval while retaining one actual append on arbitrary symbolic len and arbitrary full prefix. Constructor-prefix, length and capacity checks remain obligations. Never enumerate lengths.')
queries=[by.get('query_1_16'),by.get('query_17_22')]
rows['LPe_K017']=dict(status='CONFIRMED' if all(x and x['credit'] for x in queries) else 'OPEN',gates=queries,next='Actual Vec::from(array128/256), truncate(64+4*i); split retained live-prefix j<len from appended-byte j-len<4 for i=1..15 and i=17..21; then halve uncredited prefix observation windows. Identical KMX configuration and a failing matched control per credited split.')
(E/'KNA_ROW_CREDITS.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({r:x['status'] for r,x in rows.items()}))
