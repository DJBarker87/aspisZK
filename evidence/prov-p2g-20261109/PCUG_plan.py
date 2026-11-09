#!/usr/bin/env python3
"""PCUG_plan.py: plan equality passes against the P1f (PCQG_) emissions for every definition of PCUF_ALL_STATUS that is not PROVED on a correct basis
and has a non-axiom declaration of the (normalised) name in a PCQG run with exit 0 (PCUG_SCAN.json from PCUG_scan.py).
Gate source: PCUF_PLAN pass of the module (P2b/P2c/P2r), else P2b inputs/gate, else the P5 pass (PCT_STATUS gate_path) with the P5 input copy, NDE from P5 inputs.
Pure name presence plans the pass; the Lean compile decides. Greedy cover, at most 4 passes per module and kind."""
import json,sys,re,subprocess
from pathlib import Path
sys.dont_write_bytecode=True
import PCUG_gen_equalities as G
H=Path(__file__).resolve().parent;EV=H.parent
scan=json.load(open(H/'PCUG_SCAN.json'));idx=json.load(open(H/'PCUG_EMISSION_INDEX.json'))
PL=json.load(open(EV/'prov-p2f-20261109/PCUF_PLAN.json'));ORIG=json.load(open(EV/'prov-p2f-20261109/module_origin.json'))
P5=json.load(open(EV/'prov-p5-20261109/PCT_STATUS.json'))['modules']
ALL=json.load(open(EV/'prov-p2f-20261109/PCUF_ALL_STATUS.json'))['modules']
def variants(rel): return [rel, rel[len('aspis_core.'):] if rel.startswith('aspis_core.') else 'aspis_core.'+rel]
def show(p):
    r=subprocess.run(['git','show','research:'+p],capture_output=True,cwd=EV.parent)
    return r.stdout.decode('utf-8','replace') if r.returncode==0 else None
(H/'inputs').mkdir(exist_ok=True)
RENAME_FUNS={'RPu_FIq_Native04','RPu_FIq_Native08','RPu_FIq_Native10','RPu_FIq_Native11','RPv_PoseidonPreparedSum3Source','RPv_Qm31PackBase4Slice','RPv_RawPoseidonExtensionSlice'}
def extras_for(m):
    mm=re.fullmatch(r'RPu_FIq_Native(\d\d)',m)
    if not mm: return []
    k=int(mm.group(1));out=[]
    for j in range(1,k):
        f=EV/'prov-p2b-20261109/inputs/gate'/('RPu_FIq_Native%02d.lean'%j)
        if f.exists(): out.append(str(f.relative_to(EV)))
    return out
def rel(p): return str(Path(p).relative_to(EV))
def gate_params(m,kind):
    """-> dict(gate,gate_types,gate_extra,rename_fresh_base,gate_namespace,origin,gate_origin)"""
    if m in PL and PL[m]['passes']:
        ps=[p for p in PL[m]['passes'] if p['kind']==kind] or PL[m]['passes']
        p=ps[0];return dict(gate=p['gate'],gate_types=p['gate_types'],gate_extra=p.get('gate_extra') or [],gate_namespace=p.get('gate_namespace'),origin='PCUF_PLAN:'+PL[m]['origin'],gate_origin=p['gate_origin'])
    if m.startswith('RPu_') or m.startswith('RPv_'):
        g=EV/'prov-p2b-20261109/inputs/gate'/(m+'.lean')
        q=EV/'prov-p2b-20261109/inputs/gate/RPu_FIq_NativeTypes.lean' if m.startswith('RPu_') and m!='RPu_FIq_NativeTypes' else None
        return dict(gate=rel(g),gate_types=rel(q) if q else None,gate_extra=extras_for(m),gate_namespace=None,origin='P2b inputs',gate_origin='prov-p2b-20261109/inputs/gate')
    mm=re.fullmatch(r'NDE_Reference(\d)\.Funs',m)
    if mm:
        # PCUG-C: the compiled gate NDE source is evidence/native-front2-20261028/NDE_Reference<k>/{Funs,Types}.lean (checked ops, text-identical to PCQG_E017/E018); P5's gate input was the wrapping NML emission
        k=mm.group(1);d=H/'inputs'
        for f in ('Funs','Types'):
            t=show('evidence/native-front2-20261028/NDE_Reference%s/%s.lean'%(k,f));assert t is not None;(d/('gate_NDE_Reference%s_%s.lean'%(k,f))).write_text(t)
        return dict(gate=rel(d/('gate_NDE_Reference%s_Funs.lean'%k)),gate_types=rel(d/('gate_NDE_Reference%s_Types.lean'%k)),gate_extra=[],gate_namespace=None,origin='native-front2 compiled gate',gate_origin='research:evidence/native-front2-20261028/NDE_Reference%s'%k)
    r=P5[m];ps=[p for p in r['passes'] if p['kind' if 'kind' in p else 'tag'] is not None][0] if False else r['passes'][0]
    safe=m.replace('.','_')
    g=EV/'prov-p5-20261109/inputs'/('gate_'+safe+ps['tag']+'.lean')
    if not g.exists(): g=EV/'prov-p5-20261109/inputs'/('gate_'+safe+'.lean')
    if not g.exists():
        t=show(ps['gate_path']);assert t is not None,(m,ps['gate_path']);g=H/'inputs'/('gate_'+safe+'.lean');g.write_text(t)
    q=None
    if ps.get('gate_types_path'):
        q=EV/'prov-p5-20261109'/ps['gate_types_path']
        assert q.exists(),q
    elif r['kind']=='single': q=g
    return dict(gate=rel(g),gate_types=rel(q) if q else None,gate_extra=[],gate_namespace=None,origin='P5',gate_origin='prov-p5-20261109/inputs ('+ps['gate_path']+')')
PREFER={'RPu_FIq_Native14':['PCQG_E009','PCQG_E015']}  # PCUG-2: the single E015 pass (14 definitions, 119 theorems) timed out at 180 s (PCUG_L017); two passes with the smaller E009 closure first
plan={}
for m,names in scan.items():
    res=dict(origin=ORIG.get(m) or ('P5' if m in P5 else None),passes=[],uncovered={},status=None)
    plan[m]=res
    kinds=sorted({h[1] for hs in names.values() for h in hs})
    for kind in kinds:
        gp=gate_params(m,kind)
        g=EV/gp['gate'];gt=g.read_text()
        if gp['gate_namespace']: gt,_=G.extract_namespace(gt,gp['gate_namespace'])
        nss=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(gt))
        if len(nss)!=1: res['status']='GATE_MULTI_NAMESPACE_%d'%len(nss);continue
        gns=nss[0];gb={b['name']:b for b in G.parse_blocks(gt) if b['kind']=='decl'}
        gset=set(gb)
        if gp['gate_types'] and kind=='Funs':
            gset|={b['name'] for b in G.parse_blocks((EV/gp['gate_types']).read_text()) if b['kind']=='decl'}
        # relative names of scope definitions whose hit kind is `kind`
        want={}
        for n,hs in names.items():
            if any(h[1]==kind for h in hs): want[n[len(gns)+1:] if n.startswith(gns+'.') else n]=n
        rem=set(want);npass=0
        pref=PREFER.get(m)
        while rem and npass<4:
            best=None
            for d,e in idx.items():
                if pref and npass<len(pref) and e['run']!=pref[npass]: continue
                nm=e.get(kind) or {}
                cov={}
                for r_ in rem:
                    for v in variants(r_):
                        if v in nm and nm[v] not in('axiom','opaque') and (r_ in gb or v in gb): cov[r_]=v;break
                if cov and (best is None or len(cov)>best[0]): best=(len(cov),d,cov)
            if best is None: break
            _,d,cov=best;e=idx[d]
            nmap={v:r_ for r_,v in cov.items() if v!=r_}
            if kind=='Funs' and gp['origin'].split(':')[-1]!='P2b' and gp['origin']!='P2b inputs':
                for t in e.get('Types',{}):
                    if t not in gset:
                        for v in variants(t):
                            if v in gset and v!=t: nmap[t]=v;break
            rn=[]
            if gp['origin']=='P2b inputs' or gp['origin'].endswith('P2b'):
                fnames=set(e.get(kind,{}))|set(e.get('Types',{}))
                if any(n.startswith('aspis_statement.') for n in fnames): rn.append('aspis_statement.=')
                if 'aspis_core.field.M31' in fnames and 'field.M31' in gb: rn.append('aspis_core.field.M31=field.M31')
                rn=['aspis_core.=','aspis_statement.=']  # PCUG-1: every P2b gate module uses unprefixed crate paths (round-1 probes L007-L011: Unknown identifier aspis_core.field.*)
                nmap={}
            npass+=1
            res['passes'].append(dict(tag='' if not res['passes'] else '_p%d'%(len(res['passes'])+1),kind=kind,fresh_dir=d,fresh_ns=e['ns'][0],run=e['run'],tool='aeneas-original-959659a6',covers=sorted(cov),
                name_map=nmap,rename_fresh=rn,gate_extra=gp['gate_extra'],gate=gp['gate'],gate_types=gp['gate_types'],gate_origin=gp['gate_origin'],gate_namespace=gp['gate_namespace'],gns=gns,only_fresh=sorted(set(cov.values())),scope=sorted(want[c] for c in cov)))
            rem-=set(cov)
        res['uncovered'][kind]=sorted(want[c] for c in rem)
    if res['status'] is None: res['status']='PLANNED' if res['passes'] else 'NO_PASS'
    print(m,res['status'],[(p['kind'],p['run'],len(p['covers'])) for p in res['passes']],{k:len(v) for k,v in res['uncovered'].items()})
Path(H/'PCUG_PLAN.json').write_text(json.dumps(plan,indent=1))
