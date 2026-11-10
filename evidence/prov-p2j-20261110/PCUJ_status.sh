#!/bin/bash
# PCUJ_status.sh: merge PCUJ_PROVED.json into PCUI_ALL_STATUS.json -> PCUJ_ALL_STATUS.json, PCUJ_STATUS.json, PCUJ_REMAINING.json, PCUJ_HAND_MODELS.json
cd "$(dirname "$0")"
python3 -B - <<'PY'
import json,copy,collections,glob
P='../prov-p2i-20261110/'
A=json.load(open(P+'PCUI_ALL_STATUS.json'));pr=json.load(open('PCUJ_PROVED.json'))
ci_old=set(r['definition'] for r in json.load(open(P+'PCUI_STATUS.json'))['records'] if 'CONFIG_INDEP' in r['note'])
o1=set(v['theorem'] for v in json.load(open(P+'PCUI_PROVED_OTHER.json')).values())
specs={}
for f in glob.glob('PCUJ_E*_spec.json'): d=json.load(open(f));specs[d['run']]=d.get('aeneas_tool','extended')
# index
idx=collections.defaultdict(list)
for m,d in A['modules'].items():
    for k in d: idx[k].append(m)
EXTRA=json.load(open('PCUJ_EXTRA_PROVED.json')) if glob.glob('PCUJ_EXTRA_PROVED.json') else {}
pr=dict(pr,**EXTRA)
recs=[];WRAP=[]
for dfn,v in pr.items():
    ms=idx[dfn]
    assert len(ms)>=1,dfn
    m=ms[0]
    if len(ms)>1:
        ms2=[x for x in ms if x.split('.')[0].split('_')[0] in v['module']]
        m=(ms2 or ms)[0]
    old=A['modules'][m][dfn];new=copy.deepcopy(old)
    snap=dict(status=old['status'],theorem=old.get('theorem'),receipt=old.get('receipt'),configuration=old.get('configuration'),pcui_basis_note=old.get('pcui_basis_note'),decided_by=old.get('decided_by'))
    new.update(status='EQUALITY_PROVED',theorem=v['theorem'],proving_file=v['proving_file'],receipt=v['receipt'],decided_by='P2j',configuration=v['config'],required_configuration='ON',
        fresh_emission=v['fresh_dir'],aeneas_tool=specs.get(v.get('emission_run'),old.get('aeneas_tool')),supersedes=[snap]+old.get('supersedes',[]),pcuj_kind=v['kind'])
    new.pop('pcui_basis_note',None)
    new['pcuj_basis_note']={'A_O1_CLEAN':'O1_CLEAN_RECOMPILE_EXIT0','B_ON_EMISSION':'ON_EMISSION_MATCHING','C_SECOND_SHAPE_TRANSPARENT_P':'ON_EMISSION_MATCHING_SECOND_SHAPE'}.get(v['kind'],v['kind'])
    A['modules'][m][dfn]=new
    recs.append(dict(module=m,definition=dfn,was=snap['status'],was_note=snap['pcui_basis_note'],now='EQUALITY_PROVED',note=new['pcuj_basis_note'],theorem=v['theorem'],receipt=v['receipt'],kind=v['kind']))
# the 9 definitions that PCUI_ called CONFIG_INDEPENDENT but whose callee closure has plain-operator arithmetic (gate = wrapping, ON emission = checked)
WR=json.load(open('PCUJ_WRAPPING_CLOSURE.json'))
for dfn in WR['definitions']:
    m=idx[dfn][0];r=A['modules'][m][dfn]
    assert r.get('pcui_basis_note')=='CONFIG_INDEPENDENT_BY_TEXT_OFF_EMISSION_ONLY',dfn
    r['pcuj_basis_note']='OFF_EMISSION_WRAPPING_CLOSURE';r['pcuj_reclassified_from']='CONFIG_INDEPENDENT_BY_TEXT_OFF_EMISSION_ONLY';r['pcuj_evidence']=WR['evidence']
    r.pop('pcui_basis_note',None);r['required_configuration']='ON (not provable: see pcuj_evidence)'
    WR_rec=dict(module=m,definition=dfn);WRAP.append(WR_rec)
# totals
tot=collections.Counter();cls=collections.Counter()
for m,d in A['modules'].items():
    for k,r in d.items():
        tot[r['status']]+=1
        n=r.get('pcuj_basis_note') or r.get('pcui_basis_note')
        if r['status']=='EQUALITY_PROVED' and n: cls[n]+=1
A['totals']=dict(tot);A['pcuj_class_counts']=dict(cls)
A['pcuj_note']='PCUI_ALL_STATUS.json with the P2j (PCUJ_) records merged. EQUALITY_PROVED records carry pcuj_basis_note or pcui_basis_note: ON_EMISSION_MATCHING, O1_CLEAN_RECOMPILE_EXIT0, ON_EMISSION_MATCHING_SECOND_SHAPE, OFF_EMISSION_WRAPPING_DECL, OFF_EMISSION_WRAPPING_CLOSURE (separately counted; equality holds at OFF only), CONFIG_INDEPENDENT_BY_TEXT_OFF_EMISSION_ONLY (remaining members, if any).'
A['target_established']=False
json.dump(A,open('PCUJ_ALL_STATUS.json','w'))
json.dump(dict(schema='PCUJ_STATUS/1',target_established=False,records=recs,off_wrapping_closure=WR['definitions']),open('PCUJ_STATUS.json','w'),indent=1)
print(len(recs),'records;',dict(cls),dict(tot))
# remaining
R=json.load(open(P+'PCUI_REMAINING.json'));done=set(pr)
items=[i for i in R['items'] if i['definition'] not in done]
SH=json.load(open('PCUJ_SECOND_SHAPES.json'))
for i in items:
    s=SH['by_definition'].get(i['definition']) or SH['by_class'].get(i['cls'])
    if s: i['pcuj_second_shape']=s
    wbn=SH.get('wrong_basis_notes',{}).get(i['definition'])
    if wbn: i['pcuj_note']=wbn
R['items']=items;R['schema']='PCUJ_REMAINING/1';R['counts']=dict(collections.Counter(i['cls'] for i in items));R['target_established']=False
json.dump(R,open('PCUJ_REMAINING.json','w'),indent=1)
print('remaining',len(items),R['counts'])
HM=json.load(open(P+'PCUI_HAND_MODELS.json'));HM['schema']='PCUJ_HAND_MODELS/1'
HM['pcuj_note']='Unchanged from PCUI_HAND_MODELS.json; P2j added no hand model. The ShrAmt bridge (OFF only) is no longer needed by any P2j-credited definition; the 2 PCUI definitions that depend on it (OFF_EMISSION_WRAPPING_DECL) are unchanged.'
json.dump(HM,open('PCUJ_HAND_MODELS.json','w'),indent=1)
PY
