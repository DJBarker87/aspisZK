import json,collections
E='..'
p=json.load(open(E+'/prov-p6w-20261110/PCXH_PROVENANCE.json'))['per_definition_class']
st=json.load(open(E+'/prov-p2j-20261110/PCUJ_ALL_STATUS.json'))['modules']
mods=["AdapterRwModel","AspisR1AdapterReconstruct.Types","S1ClaimBorrowedAbiNativeV1","CurrentClaimSumModel","CurrentCompactCallerTypesV1","S1ClaimOwnedNestedModelV1"]
def cause(r,mod,d):
    o=(r or {}).get('open_reason') or ''
    if o.startswith('NO_FRESH_EMISSION'): c='NO_FRESH_EMISSION'
    elif o.startswith('TEXT_ONLY_NOT_COMPARED') or o.startswith('TEXT_IDENTICAL_ONLY'): c='TYPES' if ('Types' in mod or True) and any(t in d for t in ()) else 'TYPES_TEXT_ONLY'
    elif o.startswith('NOT_PROVED_P3: HAND_ADAPTED'): c='PARAMETRIC_OPS'
    elif o.startswith('EMITTED_NOT_COMPARED'): c='EMITTED_NOT_COMPARED'
    elif o.startswith('COMPARE_FAILED'): c='COMPARE_FAILED'
    else: c=o.split(':')[0] or 'UNCLASSIFIED'
    return c,o
out={'schema':'PCWL_TRIAGE/1','target_established':False,'modules':{}}
for m in mods:
    ks=[k.split('|',1)[1] for k,v in p.items() if k.split('|')[0]==m and v=='OPEN']
    rows=[]
    for d in ks:
        r=st.get(m,{}).get(d)
        c,o=cause(r,m,d)
        rows.append(dict(definition=d,cause=c,reason=o[:200]))
    out['modules'][m]=dict(n_open=len(rows),by_cause=dict(collections.Counter(x['cause'] for x in rows)),definitions=rows)
out['already_closed_by_merged_jobs']='none of the 63 keys appear in the p2k, p3u, p3w, p3x, p5b status files (checked by grep of the module names)'
json.dump(out,open('PCWL_TRIAGE.json','w'),indent=1)
for m,v in out['modules'].items(): print(m,v['n_open'],v['by_cause'])
