#!/usr/bin/env python3
"""PCUI_status.py: merge PCUI proofs into the PCXB deployed_splitB provenance view and PCQH_ALL_STATUS; write PCUI_STATUS.json, PCUI_ALL_STATUS.json,
PCUI_REMAINING.json, PCUI_VIEW.json. Basis rule (PCUI-C1): credit when the proving emission's configuration matches the gate declaration:
 ON emission                          -> EQUALITY_PROVED, config ON
 OFF emission, decl contains wrapping_ -> EQUALITY_PROVED, config OFF (gate models plain-operator wrapping; deployed wrapping is R22's)
 OFF emission only, no wrapping_       -> EQUALITY_PROVED with basis_note CONFIG_INDEPENDENT_BY_TEXT (no plain-operator arithmetic in the declaration, or a Rust const item);
                                          counted separately, not an emission at ON."""
import json,os,re,sys,subprocess,collections,copy
sys.dont_write_bytecode=True
H=os.path.dirname(os.path.abspath(__file__));EV=os.path.dirname(H);REPO=os.path.dirname(os.path.dirname(EV))
sys.path.insert(0,EV+'/prov-p2h-20261109');import PCUH_gen_equalities as G
P=json.load(open(EV+'/prov-p6c-20261109/PCXB_PROVENANCE.json'));ALL=json.load(open(EV+'/prov-p1h-20261109/PCQH_ALL_STATUS.json'))
PART=json.load(open(EV+'/prov-p5-20261109/PCT_PARTITION.json'))
PR=json.load(open(H+'/PCUI_PROVED.json'));PT=json.load(open(H+'/PCUI_PROVED_TYPES.json'));PO=json.load(open(H+'/PCUI_PROVED_OTHER.json'))
def gitshow(p):
    r=subprocess.run(['git','-C',REPO,'show','research:'+p],capture_output=True,text=True);return r.stdout if r.returncode==0 else None
gate_cache={}
def gate_decl(mn,dn):
    if mn not in gate_cache:
        txt=None
        for c in PART['modules'].get(mn,{}).get('candidates',[]):
            for p in c['paths']:
                txt=gitshow(p)
                if txt: break
            if txt: break
        ns=(re.findall(r'(?m)^namespace\s+(\S+)',txt or '') or [''])[0]
        gate_cache[mn]=(ns,{b['name']:b for b in G.parse_blocks(txt or '') if b['kind']=='decl'})
    ns,bl=gate_cache[mn];rel=dn[len(ns)+1:] if dn.startswith(ns+'.') else dn
    b=bl.get(rel);return b['text'] if b else ''
out_status={};basis=collections.Counter();changes=[]
newP=copy.deepcopy(P)
for src,PRV in (('wrong_basis',PR),('type_text_only',PT),('failed_or_other',PO)):
    for dn,pv in PRV.items():
        mn=pv['module']
        rec=newP['modules'].get(mn,{}).get('definitions',{}).get(dn)
        if rec is None: continue
        was=(rec['status'],rec.get('open_class'),(rec.get('open_reason') or '')[:60])
        cfg=pv['config'];text=gate_decl(mn,dn)
        if cfg=='ON': note='ON_EMISSION_MATCHING';bcls='ON'
        elif 'wrapping_' in text: note='OFF_EMISSION_WRAPPING_DECL';bcls='OFF'
        else: note='CONFIG_INDEPENDENT_BY_TEXT_OFF_EMISSION_ONLY';bcls='OFF_CI'
        basis[(src,note)]+=1
        rec.update(status='EQUALITY_PROVED',pcui_basis_note=note,configuration='ON' if cfg=='ON' else 'OFF',theorem=pv['theorem'],proving_file=pv['proving_file'],receipt=pv['receipt'],
                   decided_by='P2i',fresh_emission=pv['fresh_dir'],pcui_source=src,superseded_record=dict(status=was[0],open_class=was[1],open_reason=was[2]))
        rec.pop('open_reason',None);rec.pop('open_class',None)
        changes.append(dict(module=mn,definition=dn,was=was,now='EQUALITY_PROVED',note=note,theorem=pv['theorem']))
# module rollups
def rollup(m):
    st=collections.Counter(d['status'] for d in m['definitions'].values() if d['in_splitB_cone']);m['counts_splitB']=dict(st)
    if not st: return 'NO_ANNOTATED_DEFINITION_REACHED'
    if st.get('OPEN') or st.get('HAND_ADAPTED') or st.get('NO_FROZEN_COUNTERPART'): return 'OPEN'
    if set(st)<={'RECEIPTED'}: return 'RECEIPTED'
    if set(st)<={'EQUALITY_PROVED','RECEIPTED'}: return 'EQUALITY_PROVED'
    return 'CONDITIONAL'
before=collections.Counter(m['rollup'] for m in P['modules'].values() if m['in_splitB_cone']);flips=[]
for mn,m in newP['modules'].items():
    if not m['in_splitB_cone']: continue
    old=m['rollup'];new=rollup(m)
    if new!=old and any(c['module']==mn for c in changes): flips.append((mn,old,new))
    if any(c['module']==mn for c in changes): m['rollup_pcui']=new
sb=collections.Counter(d['status'] for m in newP['modules'].values() for d in m['definitions'].values() if d['in_splitB_cone'])
sb0=collections.Counter(d['status'] for m in P['modules'].values() for d in m['definitions'].values() if d['in_splitB_cone'])
wb_left=sum(1 for m in newP['modules'].values() for d in m['definitions'].values() if d['in_splitB_cone'] and d['status']=='OPEN' and d.get('open_class')=='WRONG_BASIS')
view=dict(schema='PCUI_VIEW/1',target_established=False,base='prov-p6c-20261109/PCXB_PROVENANCE.json',
          splitB_definitions_before=dict(sb0),splitB_definitions_after=dict(sb),
          rows_that_became_clean_definition_count=len(changes),basis_breakdown={f'{a}:{b}':n for (a,b),n in basis.items()},
          wrong_basis_open_before=119,wrong_basis_open_after=wb_left,module_rollup_flips=flips,
          rows_note='Row-level (599) recomputation needs the PCO row->module reach tables that PCXB kept in scratch (not committed); definition and module counts only.')
json.dump(view,open(H+'/PCUI_VIEW.json','w'),indent=1)
json.dump(dict(schema='PCUI_STATUS/1',target_established=False,records=changes),open(H+'/PCUI_STATUS.json','w'),indent=1)
# ALL_STATUS: PCQH_ALL_STATUS with records merged
A=copy.deepcopy(ALL);sup=[]
for c in changes:
    mod=A['modules'].get(c['module']);
    if mod is None: continue
    r=mod.get(c['definition'])
    if r is None: continue
    sup.append(dict(module=c['module'],definition=c['definition'],was=r.get('status'),was_reason=(r.get('open_reason') or '')[:80]))
    r.update(status='EQUALITY_PROVED',theorem=c['theorem'],decided_by='P2i',pcui_basis_note=c['note']);r.pop('open_reason',None)
A['schema']='PCUI_ALL_STATUS/1';A['pcui_superseded']=sup;A['pcui_note']='PCQH_ALL_STATUS.json with the P2i (PCUI_) records merged; statuses in this file keep the PCQH vocabulary; see PCUI_VIEW.json for the deployed_splitB view.'
tot=collections.Counter(r['status'] for m in A['modules'].values() for r in m.values());A['totals']=dict(tot)
json.dump(A,open(H+'/PCUI_ALL_STATUS.json','w'),indent=1)
print(json.dumps(view,indent=1)[:2500]);print(len(changes),len(sup))
