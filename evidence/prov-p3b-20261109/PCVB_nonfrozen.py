#!/usr/bin/env python3
"""PCVB_nonfrozen.py: builds PCVB_NONFROZEN_STATUS.json and PCVB_NEED_EXTRACTION.json for the 26 deployed_splitB-cone modules that
PCXA_NONFROZEN.json flags as extracted from a non-frozen source revision.
Inputs: ../prov-p6s-20261109/PCXA_NONFROZEN.json, ../prov-p2f-20261109/PCUF_ALL_STATUS.json, the P3b overlay below.
Rules: a definition is EQUALITY_PROVED only if PCUF_ALL_STATUS has a PROVED_* record with a correct basis (fresh frozen-4bb3b3f
emission, matching configuration, not superseded) or the P3b overlay proves it; detector silence is never evidence of cleanliness."""
import json,collections,sys
from pathlib import Path
E=Path(__file__).resolve().parent;R=E.parent
n=json.load(open(R/'prov-p6s-20261109/PCXA_NONFROZEN.json'))
a=json.load(open(R/'prov-p2f-20261109/PCUF_ALL_STATUS.json'))
OVER={ # P3b results, (module, definition) -> file, receipt
 ('AspisR72Sampler.Funs','AspisR72Sampler.field.M31.mul'):('PRVEq.AspisR72Sampler.Funs.field.M31.mul','PRVEq_AspisR72Sampler_Funs_P3.lean','PCVB_L040'),
 ('AspisR72Sampler.Funs','AspisR72Sampler.field.CM31.mul'):('PRVEq.AspisR72Sampler.Funs.field.CM31.mul','PRVEq_AspisR72Sampler_Funs_P3.lean','PCVB_L040'),
 ('AspisR72Sampler.Funs','AspisR72Sampler.field.CM31.square'):('PRVEq.AspisR72Sampler.Funs.field.CM31.square','PRVEq_AspisR72Sampler_Funs_P3.lean','PCVB_L040'),
 ('AspisR72Sampler.Funs','AspisR72Sampler.field.QM31.mul'):('PRVEq.AspisR72Sampler.Funs.field.QM31.mul','PRVEq_AspisR72Sampler_Funs_P3.lean','PCVB_L040'),
 ('AspisR72Sampler.Funs','AspisR72Sampler.field.QM31.square'):('PRVEq.AspisR72Sampler.Funs.field.QM31.square','PRVEq_AspisR72Sampler_Funs_P3.lean','PCVB_L040'),
}
HELPERS={ # gate-only helpers of R72Sampler with no frozen counterpart; behaviour proved where used (PRVEq_AspisR72Sampler_Funs_P3.lean)
 'AspisR72Sampler.field.r23_product_u32_bounded':'PCVB_R23.r23_eq: equals the plain checked u64 product (theorem r23_gate)',
 'AspisR72Sampler.field.r24_canonical_mul':'PCVB_R72.r24_none (any limb >= P gives none) and PCVB_R72.r24_canon (all limbs < P gives some result equal to the Karatsuba chain, via comp0..comp3)',
 'AspisR72Sampler.field.r24_canonical_mul.PP':'PCVB_R72.PP_spec: value P*P',
 'AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call':'PCVB_R72.clos_spec: value (x mod 2^31) + (x div 2^31)',
}
CRATE={'aspis_core':'crates/aspis-core','aspis_r1_cost_probe':'crates/aspis-r1-cost-probe','aspis_statement':'crates/aspis-statement'}
def frozen_path(f):
    sp=f['source_path']
    if sp.startswith('src/'):
        syms=[d['symbol'] for d in f['differing_definitions']]
        for s in syms:
            c=s.split('::')[0]
            if c in CRATE: return CRATE[c]+'/'+sp
        return 'UNMAPPED:'+sp
    return sp
def classify(rec):
    st=rec['status']
    if st.startswith('PROVED'):
        return ('EQUALITY_PROVED' if not rec.get('basis_not_correct') else 'PROVED_ON_WRONG_BASIS_UNVERIFIED')
    return {'NO_FRESH_EMISSION':'NEED_EXTRACTION','NOT_COVERED':'NEED_EXTRACTION','FAILED':'OPEN_FAILED','NOT_PROVED_P3':'OPEN_FAILED',
            'CONFIG_MISMATCH_NO_OFF_RESULT':'CONFIG_MISMATCH','TEXT_ONLY_NOT_COMPARED':'TEXT_ONLY_UNVERIFIED','TEXT_IDENTICAL_ONLY':'TEXT_IDENTICAL_NOT_PROVED',
            'TEXT_DIFFERS':'OPEN_TEXT_DIFFERS','NO_COMMON_LEAN_NAME':'NEED_EXTRACTION'}.get(st,'UNVERIFIED_'+st)
out={'schema':'PCVB_NONFROZEN_STATUS/1','target_established':False,'frozen':n['frozen'],
     'rule':'detector silence never marks a module clean; a module is ALL_DEFINITIONS_EQUALITY_PROVED only if every definition of the gate module has an EQUALITY_PROVED record against a frozen-4bb3b3f extraction with correct basis',
     'overlay':'P3b: R72Sampler field.M31.mul/CM31.mul/CM31.square/QM31.mul/QM31.square (PCVB_L040)','modules':{}}
need={'schema':'PCVB_NEED_EXTRACTION/1','target_established':False,'frozen':n['frozen'],
      'note':'No extraction run in P3b. Each entry names the gate definition whose frozen (4bb3b3f) counterpart needs a checked-configuration Aeneas emission (overflow-checks ON unless required_configuration says OFF); the lead commissions the extraction.',
      'entries':[], 'by_frozen_file':{}}
tot=collections.Counter()
for m,v in n['modules'].items():
    if not v['in_splitB_cone']: continue
    files=[]
    for f in v['files']:
        files.append({'gate_source_path':f['source_path'],'frozen_counterpart':'4bb3b3f:'+frozen_path(f),'n_definitions_checked_by_detector':f['n_definitions_checked'],
                      'detector_flagged_symbols':sorted({d['symbol'] for d in f['differing_definitions']}),
                      'identification':f.get('identification'),'matching_blobs_earliest':f.get('matching_blobs_earliest'),'best_partial_matches_top3':f.get('best_partial_matches_top3')})
    hand=n['identified_by_hand'].get(m)
    defs={}
    if m in a['modules']:
        for d,r in a['modules'][m].items():
            s=classify(r)
            ent={'status':s,'pcuf_status':r['status'],'basis_not_correct':bool(r.get('basis_not_correct')),'configuration':r.get('configuration'),
                 'required_configuration':r.get('required_configuration'),'theorem':r.get('theorem'),'file':r.get('proving_file'),'note':(r.get('note') or '')[:160]}
            if (m,d) in OVER:
                th,fl,rc=OVER[(m,d)]
                ent.update(status='EQUALITY_PROVED',pcuf_status_superseded=r['status'],theorem=th,file='evidence/prov-p3b-20261109/'+fl,receipt='evidence/prov-p3b-20261109/'+rc+'/receipt.json',basis_not_correct=False,
                           note='P3b: fresh (4bb3b3f) = gate for all inputs, standard axioms only')
            if m=='AspisR72Sampler.Funs' and d in HELPERS:
                ent.update(status='GATE_ONLY_HELPER_BEHAVIOUR_PROVED',note='no frozen counterpart exists (absent from frozen field.rs); '+HELPERS[d]+'. Absorbed into QM31.mul / CM31.mul equalities, not an equality with a frozen function.',file='evidence/prov-p3b-20261109/PRVEq_AspisR72Sampler_Funs_P3.lean',receipt='evidence/prov-p3b-20261109/PCVB_L040/receipt.json')
            defs[d]=ent
    else:
        for sym,lst in v['status_of_flagged_definitions'].items():
            for it in lst:
                defs[it['definition']]={'status':'UNVERIFIED_RECEIPTED_ONLY' if it['status']=='RECEIPTED' else 'UNVERIFIED_'+it['status'],'pcuf_status':None,
                    'note':'module not in PCUF_ALL_STATUS (no fresh = gate equality attempted); PCXA status '+it['status'],'flagged_symbol':sym}
    if not defs:
        for f in v['files']:
            for d_ in sorted({x['symbol'] for x in f['differing_definitions']}):
                defs['FLAGGED_SYMBOL '+d_]={'status':'UNVERIFIED_RECEIPTED_ONLY','pcuf_status':None,'note':'module has 2 receipted definitions (PCXA module status RECEIPTED) and no PCUF record; the detector flags this symbol; no fresh = gate equality exists'}
    c=collections.Counter(x['status'] for x in defs.values())
    ok=all(x['status'] in ('EQUALITY_PROVED','GATE_ONLY_HELPER_BEHAVIOUR_PROVED') for x in defs.values()) and bool(defs)
    verdict='ALL_DEFINITIONS_EQUALITY_PROVED' if ok else ('UNVERIFIED_NO_DEFINITION_RECORDS' if not defs else 'OPEN')
    out['modules'][m]={'group':v['group'],'in_CLOSED_root_cone':v['in_CLOSED_root_cone'],'verdict':verdict,'source_blob_identified':(hand or {}).get('identified_blob','NOT_IDENTIFIED (no history blob matches all detector ranges)'),
        'source_blob_how':(hand or {}).get('how'),'files':files,'definition_counts':dict(c),'definitions':defs}
    tot[verdict]+=1
    for d,x in defs.items():
        if x['status'] in ('NEED_EXTRACTION','UNVERIFIED_RECEIPTED_ONLY','TEXT_ONLY_UNVERIFIED') or x['status'].startswith('UNVERIFIED_'):
            ff=sorted({fl['frozen_counterpart'] for fl in files})
            need['entries'].append({'module':m,'gate_definition':d,'status':x['status'],'candidate_frozen_files':ff,'required_configuration':x.get('required_configuration') or 'ON',
                                    'gate_namespace_hint':d.rsplit('.',1)[0]})
            for f_ in ff: need['by_frozen_file'].setdefault(f_,{'modules':set(),'n':0})['modules'].add(m); need['by_frozen_file'][f_]['n']+=1
for k,vv in need['by_frozen_file'].items(): vv['modules']=sorted(vv['modules'])
out['module_verdict_counts']=dict(tot)
out['n_modules']=len(out['modules'])
need['n_entries']=len(need['entries'])
(E/'PCVB_NONFROZEN_STATUS.json').write_text(json.dumps(out,indent=1)+'\n')
(E/'PCVB_NEED_EXTRACTION.json').write_text(json.dumps(need,indent=1)+'\n')
print(out['n_modules'],out['module_verdict_counts'],need['n_entries'])
for m,x in out['modules'].items(): print(m,x['verdict'],x['definition_counts'])
