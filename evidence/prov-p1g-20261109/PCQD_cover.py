#!/usr/bin/env python3
import json,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;EV=E.parent
idx=json.loads((E/'PCQD_INDEX.json').read_text())
need=json.loads((EV/'prov-p3b-20261109/PCVB_NEED_EXTRACTION.json').read_text())['entries']
names={}
for d,v in idx.items():
    if v['superseded_by']:continue
    for n,k in v['defs'].items():names.setdefault(n,[]).append(dict(run=v['run'],tool=v['tool'],kind=k,dir=d))
res=[]
for e in need:
    g=e['gate_definition']
    tail=g.split('.')[1:] if not g.startswith('FLAGGED') else []
    hit=[]
    for n in names:
        nt=n.split('.')
        if tail and (nt==tail or (len(tail)>=2 and nt[-len(tail):]==tail) or (len(nt)>=2 and nt[-len(tail):]==tail)):
            hit+= [dict(name=n,**h) for h in names[n]]
    res.append(dict(entry=e,hits=hit))
json.dump(res,open(E/'PCQD_cover_raw.json','w'),indent=0)
c=sum(1 for r in res if r['hits'])
print(c,len(res))
for r in res:
    if r['hits']:print(r['entry']['gate_definition'],'<=',[(h['name'],h['run'],h['kind']) for h in r['hits']][:3])
