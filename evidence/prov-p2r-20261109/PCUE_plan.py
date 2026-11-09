#!/usr/bin/env python3
"""PCUE_plan.py: plan (module, overflow-on emission, gate source) passes for every module of P2a and P2d.
Gate source: the file P2a/P2d used (P2a gate_src, P2d inputs/gate_*), else a partition candidate read with `git show research:<path>`.
Coverage: reached definitions of the module (PCUD_PARTITION) whose relative name (or the recorded prefix variant) is declared in the overflow-on emission
AND is a def-like/structure declaration of the gate source. Greedy cover, at most 4 passes per module. Pure name presence; the Lean compile decides equality."""
import json,sys,re,subprocess,collections
from pathlib import Path
sys.dont_write_bytecode=True
import PCUE_gen_equalities as G
H=Path(__file__).resolve().parent;EV=H.parent
idx=json.load(open(H/'PCUE_EMISSION_INDEX.json'))
P=json.load(open(EV/'prov-p2d-20261109/PCUD_PARTITION.json'))['modules']
PREP=json.load(open(EV/'prov-p2d-20261109/gen_prepared.json'))
A=json.load(open(EV/'prov-p2a-20261109/PCUA_EQ_STATUS.json'))['modules']
D=json.load(open(EV/'prov-p2d-20261109/PCUD_EQ_STATUS.json'))['modules']
sys.path.insert(0,str(EV/'prov-p2a-20261109'))
import importlib.util
spec=importlib.util.spec_from_file_location('PCUA_jobs',EV/'prov-p2a-20261109/PCUA_jobs.py');J=importlib.util.module_from_spec(spec);spec.loader.exec_module(J)
def show(p):
    r=subprocess.run(['git','show','research:'+p],capture_output=True,cwd=EV.parent)
    return r.stdout.decode('utf-8','replace') if r.returncode==0 else None
def variants(rel):
    v=[rel]
    if rel.startswith('aspis_core.'): v.append(rel[len('aspis_core.'):])
    else: v.append('aspis_core.'+rel)
    return v
def gate_sources(m):
    """-> (gate_text, gate_types_text or None, origin) """
    ja=[j for j in J.JOBS.values() if j['M']==m]
    if ja:
        j=ja[0];g=EV/'prov-p2a-20261109/gate_src'/j['gate'];t=EV/'prov-p2a-20261109/gate_src'/j['types'] if 'types' in j else None
        return g.read_text(),(t.read_text() if t else None),str(g.relative_to(EV))
    r=PREP.get(m)
    if r and r['passes']:
        ps=r['passes'][0];safe=m.replace('.','_')+ps['tag'];g=EV/'prov-p2d-20261109/inputs'/('gate_'+safe+'.lean')
        gt=EV/'prov-p2d-20261109/inputs'/('gatetypes_'+safe+'.lean')
        return g.read_text(),(gt.read_text() if gt.exists() else None),str(g.relative_to(EV))
    for c in P[m]['candidates']:
        t=show(c['paths'][0])
        if t and len(re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(t)))==1:
            tp=c['paths'][0].replace('Funs.lean','Types.lean');tt=show(tp) if tp!=c['paths'][0] else None
            return t,tt,'research:'+c['paths'][0]
    return None,None,None
_gs=gate_sources
def gate_sources(m):
    g,t,o=_gs(m)
    if g is not None and t is None and m.endswith('.Funs'):
        sib=m[:-5]+'.Types'
        if sib in P:
            sg,_,so=_gs(sib)
            if sg is not None: return g,sg,o
    return g,t,o
def kind_of(m): return 'Types' if m.endswith('Types') or m in('AdapterRwTypes','S1M31EmbeddingSourceV1') and False else ('Funs' if m.endswith('Funs') else 'single')
if __name__=='__main__':
    mods=list(dict.fromkeys(list(A)+list(D)))
    plan={}
    for m in mods:
        if m not in P: print('NOPART',m);continue
        gt,gtt,origin=gate_sources(m)
        if gt is None: plan[m]=dict(status='GATE_SOURCE_UNAVAILABLE',passes=[]);print(m,'NO_GATE_SOURCE');continue
        ns=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(gt))
        if len(ns)!=1: plan[m]=dict(status='GATE_MULTI_NAMESPACE_%d'%len(ns),passes=[],origin=origin);print(m,'ns',ns);continue
        gns=ns[0];gb={b['name']:b for b in G.parse_blocks(gt) if b['kind']=='decl'}
        reached=[n[len(gns)+1:] for n in P[m]['reached_definitions'] if n.startswith(gns+'.')]
        other=[n for n in P[m]['reached_definitions'] if not n.startswith(gns+'.')]
        if m.endswith('.Types') or m.endswith('Types') and m not in('CurrentCompactCallerTypesV1','SelectedWideViewTypesV1','EbyKPushExplicitTypesV1','ClaimsUnrolledParentTypes'): kinds=['Types']
        elif m.endswith('.Funs') or m.endswith('Funs'): kinds=['Funs']
        else: kinds=['Funs','Types']   # single-file gate modules: both kinds, separate passes
        ja=[j for j in J.JOBS.values() if j['M']==m]
        if ja and ja[0].get('kind')=='types': kinds=['Types']
        rem=set(reached);passes=[]
        for kind in kinds:
          while rem and len(passes)<6:
            best=None
            for e,ent in idx.items():
                names=ent.get(kind)
                if not names: continue
                cov={}
                for rel in rem:
                    for v in variants(rel):
                        if v in names and names[v] not in ('axiom','opaque') and (v in gb or rel in gb):
                            cov[rel]=v;break
                key=(len(cov),)
                if cov and (best is None or key>best[0]): best=(key,e,cov)
            if best is None: break
            _,e,cov=best
            nm={v:rel for rel,v in cov.items() if v!=rel}
            if kind=='Funs':   # PCUE name map for carrier types: fresh Types name -> gate name (variant), when the gate lacks the fresh name
                gset=set(gb)|(set(b['name'] for b in G.parse_blocks(gtt) if b['kind']=='decl') if gtt else set())
                for t in idx[e].get('Types',{}):
                    if t not in gset:
                        for v in variants(t):
                            if v in gset and v!=t: nm[t]=v;break
            passes.append(dict(tag='' if not passes else '_p%d'%(len(passes)+1),kind=kind,fresh_dir=e,fresh_ns=idx[e]['ns'][0],run=idx[e]['run'],covers=sorted(cov),
                               name_map=nm))
            rem-=set(cov)
        plan[m]=dict(status='PLANNED' if passes else 'NO_OVERFLOW_ON_EMISSION',kinds=kinds,gate_ns=gns,gate_origin=origin,has_types_source=gtt is not None,passes=passes,uncovered=sorted(rem),reached_outside_gate_ns=other,n_reached=len(reached))
        print(m,kinds,plan[m]['status'],[ (p['run'],p['kind'],len(p['covers'])) for p in passes],'uncovered',len(rem))
    Path('PCUE_PLAN.json').write_text(json.dumps(plan,indent=1))
