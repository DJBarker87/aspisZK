#!/bin/bash
# PCUJ_PLAN.json: the 29 CONFIG_INDEPENDENT_BY_TEXT_OFF_EMISSION_ONLY definitions, planned against the new ON emissions.
cd "$(dirname "$0")"
python3 -B - <<'PY'
import json,re
P='../prov-p2i-20261110/'
plan=json.load(open(P+'PCUI_PLAN.json'));st=json.load(open(P+'PCUI_STATUS.json'))['records']
ci=set(r['definition'] for r in st if 'CONFIG_INDEP' in r['note'])
ON={'AdapterRwModel':'prov-p2j-20261110/PCUJ_E007_emitted/raw/NMX_registry','AspisR1RecordParser.Funs':'prov-p2j-20261110/PCUJ_E005_emitted/raw/NMH_wide_decode',
 'NHT_Constants':'prov-p2j-20261110/PCUJ_E001_emitted/raw/NHR_tx2_common','NJS_Extract.Funs':'prov-p2j-20261110/PCUJ_E003_emitted/raw/NJS_Extract','NMP_prepare.Funs':'prov-p2j-20261110/PCUJ_E003_emitted/raw/NJS_Extract',
 'NNG_verify_finish.Funs':'prov-p2j-20261110/PCUJ_E002_emitted/raw/NHR_verify_finish','R1ExtractedM31Parser':'prov-p2j-20261110/PCUJ_E004_emitted/raw/NMH_field_decode'}
out={};n=0
for m,v in plan.items():
    if m not in ON: continue
    for ps in v['passes']:
        if 'OFF' not in ps['config']: continue
        only=[o for o in ps['only'] if (v['namespace']+'.'+o) in ci or (m+'.'+o) in ci]
        if not only: continue
        n+=len(only)
        out.setdefault(m,dict(gate_source=v['gate_source'],namespace=v['namespace'],passes=[]))['passes'].append(dict(fresh_dir=ON[m],config='ON',only=only,was=ps['fresh_dir']))
print(n,'definitions');json.dump(out,open('PCUJ_PLAN.json','w'),indent=1)
PY
