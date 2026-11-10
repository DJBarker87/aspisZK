#!/usr/bin/env python3
"""PCUI_plan.py: choose, per gate module, a greedy cover of the WRONG_BASIS definitions by emissions (ON preferred).
Output PCUI_PLAN.json: module -> passes [{fresh_dir, config, only:[rel names]}], uncovered [...]."""
import json,collections,os,sys
sys.dont_write_bytecode=True
H=os.path.dirname(os.path.abspath(__file__))
SET=os.environ.get('PCUI_SET','wb');B=json.load(open(H+{'types':'/PCUI_TYPEBASIS_CANDIDATES.json','other':'/PCUI_OTHERBASIS_CANDIDATES.json','wb':'/PCUI_BASIS_CANDIDATES.json'}[SET]))
plan={}
for mn,m in B.items():
    defs=m['defs']; rem={x['rel']:x for x in defs if x['hits']}
    passes=[]
    for want in ('ON','OFF_DEFAULT'):
        while True:
            cnt=collections.Counter()
            for r,x in rem.items():
                for (er,cfg,f) in x['hits']:
                    if cfg==want: cnt[er]+=1
            if not cnt: break
            er,_=cnt.most_common(1)[0]
            got=[r for r,x in rem.items() if any(h[0]==er and h[1]==want for h in x['hits'])]
            passes.append(dict(fresh_dir=er,config=want,only=sorted(got)))
            for r in got: rem.pop(r)
    plan[mn]=dict(gate_source=m.get('gate_source'),namespace=m.get('namespace'),passes=passes,
                  uncovered=[x['rel'] for x in defs if x['rel'] in rem or not x['hits']])
json.dump(plan,open(H+{'types':'/PCUI_TYPEPLAN.json','other':'/PCUI_OTHERPLAN.json','wb':'/PCUI_PLAN.json'}[SET],'w'),indent=1)
for mn,p in plan.items(): print(mn,[(q['fresh_dir'].split('/')[-3:] ,q['config'],len(q['only'])) for q in p['passes']],'uncovered',len(p['uncovered']))
