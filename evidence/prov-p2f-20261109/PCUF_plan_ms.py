#!/usr/bin/env python3
"""PCUF_plan_ms.py: plan passes for the P2r modules whose gate source has several namespaces (GATE_SOURCE_UNAVAILABLE, scope item 3).
One pass per (gate namespace holding reached definitions, emission); --gate-namespace selects the namespace. Adds the modules to PCUF_PLAN.json."""
import json,sys,re
from pathlib import Path
sys.dont_write_bytecode=True
import PCUF_gen_equalities as G
import PCUF_plan0 as PL
H=Path(__file__).resolve().parent;EV=H.parent
idx=json.load(open(H/'PCUF_EMISSION_INDEX.json'));reached_all=json.load(open(H/'module_reached.json'))
plan=json.load(open(H/'PCUF_PLAN.json'))
MS=['CurrentWideEqSemanticV7','ClaimsUnrolledParentTypes','CurrentClaimSumModel','NFN_ExtractedGeometry','S8Kani2MutableSource']
def variants(rel): return [rel, rel[len('aspis_core.'):] if rel.startswith('aspis_core.') else 'aspis_core.'+rel]
for m in MS:
    cand=PL.P[m]['candidates'][0]['paths'][0];t=PL.show(cand)
    p=H/'inputs'/('gate_'+m+'.lean');p.parent.mkdir(exist_ok=True);p.write_text(t)
    nss=[]
    for x in re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(t)):
        if x not in nss: nss.append(x)
    res=dict(origin='P2r',selected_reason={'GATE_SOURCE_UNAVAILABLE':len(reached_all[m])},passes=[],status=None,gate_namespaces=nss,gate_origin='research:'+cand)
    for ns in nss:
        reached=[n[len(ns)+1:] for n in reached_all[m] if n.startswith(ns+'.')]
        if not reached: continue
        gt,_=G.extract_namespace(t,ns);gb={b['name']:b for b in G.parse_blocks(gt) if b['kind']=='decl'}
        for kind in ('Funs','Types'):
            rem=set(reached)
            while rem and len(res['passes'])<8:
                best=None
                for e,ent in idx.items():
                    if not ent['eligible']: continue
                    names=ent.get(kind)
                    if not names: continue
                    cov={}
                    for rel in rem:
                        for v in variants(rel):
                            if v in names and names[v] not in('axiom','opaque') and (rel in gb or v in gb): cov[rel]=v;break
                    if cov and (best is None or len(cov)>best[0]): best=(len(cov),e,cov)
                if best is None: break
                _,e,cov=best
                nm={v:rel for rel,v in cov.items() if v!=rel}
                res['passes'].append(dict(tag='_ns_%s_%d'%(ns,len(res['passes'])+1),kind=kind,fresh_dir=e,fresh_ns=idx[e]['ns'][0],run=idx[e]['run'],tool=idx[e]['tool'],covers=sorted(cov),
                    name_map=nm,rename_fresh=[],gate_extra=[],gate=str(p.relative_to(EV)),gate_types=str(p.relative_to(EV)),gate_origin=res['gate_origin'],gate_namespace=ns))
                rem-=set(cov)
        res.setdefault('uncovered',{})[ns]=sorted(set(reached)-{c for ps in res['passes'] if ps.get('gate_namespace')==ns for c in ps['covers']})
    res['status']='PLANNED' if res['passes'] else 'NO_ELIGIBLE_EMISSION'
    plan[m]=res
    print(m,nss,res['status'],[(q['run'],q['kind'],q['gate_namespace'],len(q['covers'])) for q in res['passes']],{k:len(v) for k,v in res['uncovered'].items()})
Path(H/'PCUF_PLAN.json').write_text(json.dumps(plan,indent=1))
