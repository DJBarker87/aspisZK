#!/usr/bin/env python3
"""PCUH_plan.py: build PCUH_PLAN.json (generator passes) from PCQD_COVERAGE.json FRESH_PRESENT_PCQD entries.
One pass per (gate module, fresh emission directory, kind). Names: fresh name = frozen_name_tail; gate namespace = prefix of gate_definition."""
import json,re,sys,collections
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;EV=H.parent
cov=json.load(open(EV/'prov-p1g-20261109/PCQD_COVERAGE.json'))
INP='prov-p2h-20261109/inputs/'
GATE={ # module -> (gate, gate_types or None for the same file)
 'AdapterRwModel':('prov-p5-20261109/inputs/gate_AdapterRwModel.lean','prov-p2r-20261109/inputs/gate_AdapterRwTypes.lean'),
 'AspisR1AdapterReconstruct.Funs':(INP+'gate_AspisR1AdapterReconstruct_Funs.lean',INP+'gate_AspisR1AdapterReconstruct_Types_repo.lean'),
 'AspisR1AdapterReconstruct.Types':('prov-p2c-20261109/inputs/gate_AspisR1AdapterReconstruct_Types.lean',None),
 'AspisR1DecodeKFullV10.Funs':(INP+'gate_AspisR1DecodeKFullV10_Funs.lean','prov-p2d-20261109/inputs/gate_AspisR1DecodeKFullV10_Types.lean'),
 'AspisR72Sampler.Funs':('prov-p2d-20261109/inputs/gate_AspisR72Sampler_Funs.lean','prov-p2f-20261109/inputs/gatetypes_AspisR72Sampler_Funs.lean'),
 'AspisR72Sampler.Types':('prov-p2d-20261109/inputs/gate_AspisR72Sampler_Types.lean',None),
 'CurrentCompactCallerTypesV1':('prov-p2d-20261109/inputs/gate_CurrentCompactCallerTypesV1.lean',None),
 'NFN_ExtractedGeometry':('prov-p2f-20261109/inputs/gate_NFN_ExtractedGeometry.lean',None),
 'NGN_Emitted':('prov-p2d-20261109/inputs/gate_NGN_Emitted.lean',None),
 'NJA_CountBody':('prov-p2d-20261109/inputs/gate_NJA_CountBody.lean',None),
 'Port3_NativeGeometryBody':('prov-p2d-20261109/inputs/gate_Port3_NativeGeometryBody.lean',None),
 'Port4C_NativePrefix':(INP+'gate_Port4C_NativePrefix.lean',None),
 'Port5Q2_ReaderWeights':('prov-p2d-20261109/inputs/gate_Port5Q2_ReaderWeights.lean',None),
 'S1NativeCompactModelV1':('prov-p2d-20261109/inputs/gate_S1NativeCompactModelV1.lean',None),
}
def decls(text):
    return re.findall(r'(?m)^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(def|structure|inductive|abbrev|axiom)\s+(\S+)',text)
passes=collections.defaultdict(list);unres=[];nmaps=collections.defaultdict(dict)
for e in cov['entries']:
    if e['status']!='FRESH_PRESENT_PCQD' or e['module'] not in GATE: continue
    ev=e['evidence'][0]; d=ev['dir']; tail=e['frozen_name_tail']
    gd=e['gate_definition']
    gtext=(EV/GATE[e['module']][0]).read_text()
    nss=re.findall(r'(?m)^namespace\s+(\S+)',gtext)
    gns=max([n for n in nss if gd.startswith(n+'.')],key=len,default=None)
    funs=(EV/d/'Funs.lean').read_text() if (EV/d/'Funs.lean').exists() else ''
    types=(EV/d/'Types.lean').read_text() if (EV/d/'Types.lean').exists() else ''
    fn={n for k,n in decls(funs)}; tn={n for k,n in decls(types)}
    kind=None; fname=None
    for cand in (tail,'aspis_r1_cost_probe.'+tail,'aspis_core.'+tail):
        if cand in fn: kind,fname='Funs',cand;break
        if cand in tn: kind,fname='Types',cand;break
    if not kind or gns is None: unres.append((e['module'],gd,tail,ev['kind'],gns)); continue
    grel=gd[len(gns)+1:]
    if fname!=grel: nmaps[(e['module'],d,kind,gns)][fname]=grel
    tail=fname
    passes[(e['module'],d,kind,gns)].append(tail)
plan={}
for (m,d,kind,gns),names in sorted(passes.items()):
    ns=re.search(r'(?m)^namespace\s+(\S+)',(EV/d/('Funs.lean' if kind=='Funs' else 'Types.lean')).read_text()).group(1)
    run=d.split('/')[1].split('_emitted')[0]
    g,gt=GATE[m]
    ent=plan.setdefault(m,dict(passes=[]))
    tag='' if not ent['passes'] else '_p%d'%(len(ent['passes'])+1)
    ent['passes'].append(dict(tag=tag,kind=kind,fresh_dir=d,fresh_ns=ns,run=run,gate=g,gate_types=(gt or g) if kind=='Funs' else None,gate_namespace=gns,gns=gns,
        name_map=nmaps[(m,d,kind,gns)],rename_fresh=[],gate_extra=[],only_fresh=sorted(set(names))))
OVERRIDES={ # (module, tag) -> extra keys (hand-written inputs)
 ('AspisR72Sampler.Funs',''):dict(preamble='inputs/R72_preamble.lean',given='inputs/R72_given.json'),
 ('S1NativeCompactModelV1',''):dict(given='inputs/S1_given.json'),
 ('NFN_ExtractedGeometry',''):dict(extra_import=['PRVH_WrapAdd'],fresh_prelude='inputs/NFN_prelude.lean',given='inputs/NFN_given.json'),
 ('NFN_ExtractedGeometry','_p2'):dict(extra_import=['PRVH_WrapAdd'],fresh_prelude='inputs/NFN_prelude.lean',given='inputs/NFN_p2_given.json'),
}
for m,v in plan.items():
    for ps in v['passes']: ps.update(OVERRIDES.get((m,ps['tag']),{}))
json.dump(plan,open(H/'PCUH_PLAN.json','w'),indent=1)
print(sum(len(v['passes']) for v in plan.values()),'passes;',len(unres),'unresolved')
for u in unres: print('UNRES',u)
for m,v in plan.items():
    for ps in v['passes']: print(m,ps['tag'],ps['kind'],ps['run'],ps['gate_namespace'],len(ps['only_fresh']))
