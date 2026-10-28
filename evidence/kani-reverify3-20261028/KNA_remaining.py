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
 rows[row]['remaining']=[dict(range=[lo,hi],next_split=[[lo,(lo+hi)//2],[(lo+hi)//2,hi]],status='UNRUN' if not gate else gate['positive']+'/'+gate['control']) for (lo,hi),gate in zip([(0,884),(884,1768)],splits) if not (gate and gate['credit'])] if not (p and p['credit']) else []
queries=[by.get('query_'+str(cap)+'_'+suffix) for cap,suffixes in [(128,['0_64','64_124','tail']),(256,['0_64','64_128','128_148','tail'])] for suffix in suffixes]
rows['LPe_K017']=dict(status='CONFIRMED' if all(x and x['credit'] for x in queries) else 'OPEN',gates=queries,next='Actual Vec::from(array128/256), truncate(64+4*i), append4; retain i=1..15 or i=17..21 respectively. Halve each uncredited retained-prefix window and keep j<len for constructor and final association. Split the appended4 window into b<2 and 2<=b<4. Every replacement needs an identical failing control; never rerun a timeout unchanged.')
rows['LPe_K017']['remaining']=[]
for cap,windows in [(128,[(0,64),(64,124)]),(256,[(0,64),(64,128),(128,148)])]:
 for lo,hi in windows+[(0,4)]:
  tail=(lo,hi)==(0,4);name=f'query_{cap}_'+('tail' if tail else f'{lo}_{hi}');gate=by.get(name)
  if not (gate and gate['credit']):rows['LPe_K017']['remaining'].append(dict(name=name,capacity=cap,index='b=j-len' if tail else 'j<len',range=[lo,hi],next_split=[[lo,(lo+hi)//2],[(lo+hi)//2,hi]],status='UNRUN' if not gate else gate['positive']+'/'+gate['control']))
(E/'KNA_ROW_CREDITS.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({r:x['status'] for r,x in rows.items()}))
