#!/usr/bin/env python3
"""PCUF_index.py: index of the eligible fresh emissions for P2f.
Eligible: overflow-checks-ON, exit 0, not superseded (PCQF_SUPERSEDES.json): PCQ_E037,E038 (P1a), PCQC_E001,E005-E010,E012,E022,E023 (P1c),
PCQE_* exit 0 (P1d, ORIGINAL Aeneas 959659a6), PCQF_* exit 0 (P1e). Superseded dirs are recorded with eligible=false."""
import json,sys
from pathlib import Path
sys.dont_write_bytecode=True
import PCUF_gen_equalities as G
EV=Path(__file__).resolve().parent.parent
sup=json.load(open(EV/'prov-p1e-20261109/PCQF_SUPERSEDES.json'))['supersedes']
SUPERSEDED={s['superseded']:s['replacement'] for s in sup}
runs=[]
def add(prefix,pdir,rng,tool):
    for i in rng:
        run='%s_E%03d'%(prefix,i);rp=EV/pdir/run/'receipt.json'
        if not (EV/pdir/(run+'_emitted/raw')).exists(): continue
        ex=json.load(open(rp)).get('exit_status') if rp.exists() else None
        if ex!=0: continue
        runs.append((run,pdir,tool))
add('PCQ','prov-p1a-20261109',(37,38,39,40),'aeneas-b59d5188-extended')
add('PCQC','prov-p1c-20261109',range(1,26),'aeneas-b59d5188-extended')
add('PCQE','prov-p1d-20261109',range(1,20),'aeneas-original-959659a6')
add('PCQF','prov-p1e-20261109',range(1,40),'aeneas-b59d5188-extended')
# P1a/P1c ON status: PCQ_E037-E040 are overflow-on (P1a); PCQC all ON; PCQE all ON; PCQF all ON. PCQC_E013..E025 successes: only E022,E023 exit 0 besides E001-E012.
idx={}
for run,pdir,tool in runs:
    for d in sorted((EV/pdir/(run+'_emitted/raw')).glob('*')):
        e={'dir':str(d.relative_to(EV)),'run':run,'tool':tool,'overflow_checks':'ON','superseded_by':SUPERSEDED.get(run),'eligible':run not in SUPERSEDED}
        for k in ('Types','Funs'):
            p=d/(k+'.lean')
            if not p.exists(): continue
            t=p.read_text();h=G.header_info(t);bl=[b for b in G.parse_blocks(t) if b['kind']=='decl']
            e['ns']=h['namespaces']
            e[k]={b['name']:b['dkind'] for b in bl}
            q=d/(k+'External_Template.lean')
            e[k+'_ext']=G.parse_externals(q.read_text()) if q.exists() else []
        idx[e['dir']]=e
Path('PCUF_EMISSION_INDEX.json').write_text(json.dumps(idx,indent=1))
import collections
c=collections.Counter((v['run'],v['eligible']) for v in idx.values())
print(len(idx),sorted(c.items()))
