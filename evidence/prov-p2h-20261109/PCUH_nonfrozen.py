#!/usr/bin/env python3
"""PCUH_nonfrozen.py: PCUH_NONFROZEN_STATUS.json (all 26 non-frozen modules, per-definition status after P2h) and PCUH_COVERAGE_RESULT.json
(the 130 PCQD_COVERAGE entries with their P2h outcome)."""
import json,collections,sys
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;EV=H.parent
J=lambda p: json.load(open(EV/p))
nf=J('prov-p3b-20261109/PCVB_NONFROZEN_STATUS.json'); al=json.load(open(H/'PCUH_ALL_STATUS.json')); eq=json.load(open(H/'PCUH_EQ_STATUS.json'))
cov=J('prov-p1g-20261109/PCQD_COVERAGE.json'); nofz=J('prov-p1g-20261109/PCQD_NO_FROZEN_COUNTERPART.json')
nofz_defs={x['gate_definition']:x['reason'] for x in nofz['items']}
fail=J('prov-p1g-20261109/PCQD_FAILURES.json')
mine={(r['module'],r['definition']):r for r in eq['records']}
out=dict(schema='PCUH_NONFROZEN_STATUS/1',target_established=False,frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
  rule='A module is ALL_DEFINITIONS_EQUALITY_PROVED only if every definition of the gate module has an EQUALITY_PROVED record against a fresh frozen-4bb3b3f extraction on a correct basis. A module whose body the detector could not see stays UNVERIFIED until such an equality exists for each definition. Gate definitions with no frozen counterpart are listed and stay OPEN.',
  modules={},verdict_counts={},gate_defs_without_frozen_counterpart=nofz['items'])
for m,mv in nf['modules'].items():
    defs={}
    for d,r in mv['definitions'].items():
        a=al['modules'].get(m,{}).get(d)
        st=a['status'] if a else r['status']
        if d in nofz_defs: st='NO_FROZEN_COUNTERPART'
        defs[d]=dict(status=st,previous_P3b_status=r['status'],open_reason=(a or {}).get('open_reason'),theorem=(a or {}).get('theorem') or r.get('theorem'),
                     proving_file=(a or {}).get('proving_file') or r.get('file'),configuration=(a or {}).get('configuration') or r.get('configuration'),
                     required_configuration=(a or {}).get('required_configuration') or r.get('required_configuration'),decided_by=(a or {}).get('decided_by'),
                     no_frozen_counterpart_reason=nofz_defs.get(d))
    c=collections.Counter(x['status'] for x in defs.values())
    allp=all(x['status']=='EQUALITY_PROVED' for x in defs.values())
    verdict='ALL_DEFINITIONS_EQUALITY_PROVED' if allp else 'OPEN'
    out['modules'][m]=dict(group=mv['group'],in_CLOSED_root_cone=mv['in_CLOSED_root_cone'],verdict=verdict,previous_verdict=mv['verdict'],counts=dict(c),
        source_blob_identified=mv['source_blob_identified'],source_blob_how=mv.get('source_blob_how'),files=mv['files'],detector_blind_note=('UNVERIFIED: no history blob matches all detector ranges; equality only for the listed fresh-extracted definitions' if 'NOT_IDENTIFIED' in str(mv['source_blob_identified']) else None),definitions=defs)
out['verdict_counts']=dict(collections.Counter(v['verdict'] for v in out['modules'].values()))
out['definition_counts']=dict(collections.Counter(x['status'] for v in out['modules'].values() for x in v['definitions'].values()))
out['previous_definition_counts_P3b']=dict(collections.Counter(x['status'] for v in nf['modules'].values() for x in v['definitions'].values()))
json.dump(out,open(H/'PCUH_NONFROZEN_STATUS.json','w'),indent=1)
# coverage result
res=[]
for e in cov['entries']:
    gd=e['gate_definition']; m=e['module']; r=mine.get((m,gd))
    if e['status']=='FRESH_PRESENT_PCQD':
        if r: o=dict(outcome=r['status'],reason=r.get('reason_class'),detail=(r.get('reason') or '')[:160],theorem=r.get('theorem'),verifying_scope=r.get('verifying_scope'))
        else: o=dict(outcome='NOT_COMPARED_NO_PLAN',detail='gate module not in the P2h plan')
    elif e['status']=='ALREADY_COVERED': o=dict(outcome='ALREADY_COVERED',detail='fresh emission from an earlier phase; see PCUH_ALL_STATUS module record',all_status=(al['modules'].get(m,{}).get(gd.split('.',1)[-1],{}) or {}).get('status'))
    elif e['status']=='NO_FROZEN_COUNTERPART': o=dict(outcome='NO_FROZEN_COUNTERPART',detail=nofz_defs.get(gd))
    else: o=dict(outcome='OPEN',reason='NOT_OBTAINED (no fresh emission, PCQD_FAILURES)')
    res.append(dict(module=m,gate_definition=gd,p1g_status=e['status'],**o))
json.dump(dict(schema='PCUH_COVERAGE_RESULT/1',counts=dict(collections.Counter((x['p1g_status'],x['outcome']) .__str__() for x in res)),entries=res),open(H/'PCUH_COVERAGE_RESULT.json','w'),indent=1)
print(out['verdict_counts'],out['definition_counts']); print(collections.Counter((x['p1g_status'],x['outcome']) for x in res))
