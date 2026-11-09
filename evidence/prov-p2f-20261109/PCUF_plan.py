#!/usr/bin/env python3
"""PCUF_plan.py: plan equality passes for the P2f modules (selected_modules.json) against the ELIGIBLE emissions (PCUF_EMISSION_INDEX.json).
Greedy cover (at most 6 passes per module and kind) of the module's reached definitions; pure name presence, the Lean compile decides.
Gate source resolution: P2c prepared inputs, P2b inputs/gate, P2r (PCUF_plan0.gate_sources = P2a gate_src / P2d inputs / research)."""
import json,sys,re
from pathlib import Path
sys.dont_write_bytecode=True
import PCUF_gen_equalities as G
import PCUF_plan0 as PL
H=Path(__file__).resolve().parent;EV=H.parent
idx=json.load(open(H/'PCUF_EMISSION_INDEX.json'))
sel=json.load(open(H/'selected_modules.json'));origin=json.load(open(H/'module_origin.json'));reached_all=json.load(open(H/'module_reached.json'))
P2C=json.load(open(EV/'prov-p2c-20261109/gen_prepared.json'))
PART={'P2r':'prov-p2d-20261109/PCUD_PARTITION.json','P2b':'prov-p2b-20261109/PCUB_PARTITION.json','P2c':'prov-p2c-20261109/PCUC_PARTITION.json'}
def variants(rel):
    return [rel, rel[len('aspis_core.'):] if rel.startswith('aspis_core.') else 'aspis_core.'+rel]
def gate_for(m,kind):
    """-> (gate_text_path, gate_types_path|None, origin) or None"""
    o=origin[m]
    if o=='P2c':
        for key,r in P2C.items():
            if r['module']==m and r['view']==kind and r.get('passes'):
                tag=r['passes'][0]['tag'];safe=m.replace('.','_')+tag
                g=EV/'prov-p2c-20261109/inputs'/('gate_'+safe+'.lean');q=EV/'prov-p2c-20261109/inputs'/('gatetypes_'+safe+'.lean')
                return g,(q if q.exists() else None),'prov-p2c-20261109/inputs'
        return None
    if o=='P2b':
        g=EV/'prov-p2b-20261109/inputs/gate'/(m+'.lean')
        q=EV/'prov-p2b-20261109/inputs/gate/RPu_FIq_NativeTypes.lean' if m.startswith('RPu_') and m!='RPu_FIq_NativeTypes' else None
        return (g,q,'prov-p2b-20261109/inputs/gate') if g.exists() else None
    gt,gtt,org=PL.gate_sources(m)
    if gt is None: return None
    if org.startswith('research:'):
        p=H/'inputs'/('gate_'+m.replace('.','_')+'.lean');p.parent.mkdir(exist_ok=True);p.write_text(gt);g=p
        q=None
        if gtt is not None:
            q=H/'inputs'/('gatetypes_'+m.replace('.','_')+'.lean');q.write_text(gtt)
        return g,q,org
    g=EV/org;q=None
    if gtt is not None:
        if org.startswith('prov-p2a'):
            ja=[j for j in PL.J.JOBS.values() if j['M']==m][0];q=EV/'prov-p2a-20261109/gate_src'/ja['types']
        else:
            q=EV/org.replace('/gate_','/gatetypes_')
            if not q.exists():
                q=H/'inputs'/('gatetypes_'+m.replace('.','_')+'.lean');q.parent.mkdir(exist_ok=True);q.write_text(gtt)
    return g,q,org
def kinds_of(m):
    o=origin[m]
    if o=='P2c':
        return [r['view'] for r in P2C.values() if r['module']==m and r.get('passes')] or []
    if m.endswith('.Types') or m.endswith('Types') and m not in('CurrentCompactCallerTypesV1','SelectedWideViewTypesV1','EbyKPushExplicitTypesV1','ClaimsUnrolledParentTypes'): return ['Types']
    if m.endswith('.Funs') or m.endswith('Funs'): return ['Funs']
    if o=='P2b': return ['Funs']
    ja=[j for j in PL.J.JOBS.values() if j['M']==m]
    if ja and ja[0].get('kind')=='types': return ['Types']
    return ['Funs','Types']
import re as _re
def extras_for(m):
    mm=_re.fullmatch(r'RPu_FIq_Native(\d\d)',m)
    if not mm: return []
    k=int(mm.group(1));out=[]
    for j in range(1,k):
        f=EV/'prov-p2b-20261109/inputs/gate'/('RPu_FIq_Native%02d.lean'%j)
        if f.exists(): out.append(str(f.relative_to(EV)))
    return out
RENAME_FUNS={'RPu_FIq_Native04','RPu_FIq_Native08','RPu_FIq_Native10','RPu_FIq_Native11','RPv_PoseidonPreparedSum3Source','RPv_Qm31PackBase4Slice','RPv_RawPoseidonExtensionSlice'}
plan={}
for m in sel:
    kinds=kinds_of(m);reached_full=reached_all[m]
    res=dict(origin=origin[m],selected_reason={k:len(v) for k,v in sel[m].items()},passes=[],status=None)
    plan[m]=res
    rem_all=None
    gns=None
    for kind in kinds:
        gf=gate_for(m,kind)
        if gf is None:
            res['status']='GATE_SOURCE_UNAVAILABLE';continue
        g,q,org=gf
        gt=g.read_text()
        ns=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(gt))
        if len(ns)!=1: res['status']='GATE_MULTI_NAMESPACE_%d'%len(ns);continue
        gns=ns[0];gb={b['name']:b for b in G.parse_blocks(gt) if b['kind']=='decl'}
        reached=[n[len(gns)+1:] for n in reached_full if n.startswith(gns+'.')]
        rem=set(reached);npass=0
        while rem and npass<6:
            best=None
            for e,ent in idx.items():
                if not ent['eligible']: continue
                names=ent.get(kind)
                if not names: continue
                cov={}
                for rel in rem:
                    for v in variants(rel):
                        if v in names and names[v] not in('axiom','opaque') and (rel in gb or v in gb):
                            cov[rel]=v;break
                if cov and (best is None or len(cov)>best[0]): best=(len(cov),e,cov)
            if best is None: break
            _,e,cov=best
            nm={v:rel for rel,v in cov.items() if v!=rel}
            if kind=='Funs' and origin[m]!='P2b':
                gset=set(gb)|(set(b['name'] for b in G.parse_blocks(q.read_text()) if b['kind']=='decl') if q else set())
                for t in idx[e].get('Types',{}):
                    if t not in gset:
                        for v in variants(t):
                            if v in gset and v!=t: nm[t]=v;break
            rn=[]
            if origin[m]=='P2b':
                fnames=set(idx[e].get(kind,{}))|set(idx[e].get('Types',{}))
                if any(n.startswith('aspis_statement.') for n in fnames): rn.append('aspis_statement.=')
                if 'aspis_core.field.M31' in fnames and 'field.M31' in gb: rn.append('aspis_core.field.M31=field.M31')
                # PCUF: P2b gate modules use unprefixed crate paths; Funs passes of these modules strip the crate prefixes so carrier types resolve (PCUB change 3 applied to the whole prefix)
                if kind=='Funs' and m in RENAME_FUNS: rn=['aspis_core.=','aspis_statement.=']
                nm={}
            npass+=1
            res['passes'].append(dict(tag='' if not res['passes'] else '_p%d'%(len(res['passes'])+1),
                kind=kind,fresh_dir=e,fresh_ns=idx[e]['ns'][0],run=idx[e]['run'],tool=idx[e]['tool'],covers=sorted(cov),name_map=nm,rename_fresh=rn,
                gate_extra=extras_for(m),
                gate=str(g.relative_to(EV)) if str(g).startswith(str(EV)) else str(g.relative_to(H.parent)),
                gate_types=(str(q.relative_to(EV)) if q is not None else None),gate_origin=org))
            rem-=set(cov)
        res.setdefault('uncovered',{})[kind]=sorted(rem)
        res['gate_ns']=gns
    if res['status'] is None: res['status']='PLANNED' if res['passes'] else 'NO_ELIGIBLE_EMISSION'
    print(m,origin[m],res['status'],[(p['run'],p['kind'],len(p['covers'])) for p in res['passes']],{k:len(v) for k,v in res.get('uncovered',{}).items()})
Path('PCUF_PLAN.json').write_text(json.dumps(plan,indent=1))
