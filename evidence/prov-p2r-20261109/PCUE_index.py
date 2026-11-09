#!/usr/bin/env python3
"""PCUE_index.py: index the overflow-checks-on fresh emissions (P1c PCQC_E001-E012,E022,E023 and P1a PCQ_E037-E040)."""
import json,sys,re
from pathlib import Path
sys.dont_write_bytecode=True
import PCUE_gen_equalities as G
EV=Path(__file__).resolve().parent.parent
DIRS=[]
for run in ['prov-p1c-20261109/PCQC_E%03d'%i for i in list(range(1,13))+[22,23]]+['prov-p1a-20261109/PCQ_E%03d'%i for i in (37,38,39,40)]:
    for d in sorted((EV/(run+'_emitted/raw')).glob('*')):
        DIRS.append(d)
idx={}
for d in DIRS:
    e={'dir':str(d.relative_to(EV)),'run':d.parent.parent.name.replace('_emitted','')}
    for k in ('Types','Funs'):
        p=d/(k+'.lean')
        if not p.exists(): continue
        t=p.read_text();h=G.header_info(t);bl=[b for b in G.parse_blocks(t) if b['kind']=='decl']
        e['ns']=h['namespaces']
        e[k]={b['name']:b['dkind'] for b in bl}
        q=d/(k+'External_Template.lean')
        e[k+'_ext']=G.parse_externals(q.read_text()) if q.exists() else []
    idx[e['dir']]=e
Path('PCUE_EMISSION_INDEX.json').write_text(json.dumps(idx,indent=1))
for k,v in idx.items(): print(v['run'],k.split('/')[-1],len(v.get('Types',{})),len(v.get('Funs',{})),v.get('ns'))
