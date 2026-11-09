#!/usr/bin/env python3
"""PCUG_scan.py: which not-PROVED-on-correct-basis definitions of PCUF_ALL_STATUS have a declaration (non-axiom) in a P1f (PCQG_) emission with exit 0."""
import json,sys,collections
from pathlib import Path
sys.dont_write_bytecode=True
import PCUG_gen_equalities as G
H=Path(__file__).resolve().parent;EV=H.parent
A=json.load(open(EV/'prov-p2f-20261109/PCUF_ALL_STATUS.json'))['modules']
cov=json.load(open(EV/'prov-p1f-20261109/PCQG_COVERAGE.json'))
runs=[r for r,v in cov['runs_configuration'].items() if v['exit']==0]
idx={}
for r in runs:
    for d in sorted((EV/'prov-p1f-20261109'/(r+'_emitted/raw')).glob('*')):
        e={'run':r,'dir':str(d.relative_to(EV))}
        for k in ('Types','Funs'):
            p=d/(k+'.lean')
            if p.exists():
                t=p.read_text();h=G.header_info(t);e['ns']=h['namespaces']
                e[k]={b['name']:b['dkind'] for b in G.parse_blocks(t) if b['kind']=='decl'}
        idx[e['dir']]=e
Path('PCUG_EMISSION_INDEX.json').write_text(json.dumps(idx,indent=1))
def variants(rel): return [rel, rel[len('aspis_core.'):] if rel.startswith('aspis_core.') else 'aspis_core.'+rel]
def good(r): return r['status'].startswith('PROVED') and not r.get('basis_not_correct')
open_=collections.defaultdict(list)
for m,recs in A.items():
    for n,r in recs.items():
        if good(r): continue
        ns=n.split('.')[0]
        open_[m].append(n)
found={}
for m,names in open_.items():
    for n in names:
        gns=A[m][n]['definition'].split('.')[0]
        rel=n[len(gns)+1:]
        hits=[]
        for d,e in idx.items():
            for k in ('Types','Funs'):
                nm=e.get(k) or {}
                for v in variants(rel):
                    if v in nm and nm[v] not in('axiom','opaque'): hits.append((d,k,v,nm[v]));break
        if hits: found.setdefault(m,{})[n]=hits
tot=sum(len(v) for v in found.values())
print(len(open_),sum(len(v) for v in open_.values()),'open;',len(found),'modules',tot,'defs with P1f hits')
for m,v in found.items(): print(m,len(v),sorted({h[0].split('/')[-1] for hs in v.values() for h in hs}))
Path('PCUG_SCAN.json').write_text(json.dumps(found,indent=1))
