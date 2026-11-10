#!/usr/bin/env python3
"""PCQH_finalize.py: builds PCQH_EQ_STATUS / ALL_STATUS / COVERAGE / FAILURES / REMAINING / HAND_MODELS / CLASSIFICATIONS / TOOLS / SCOPE_SUMMARY."""
import json,re,copy
from pathlib import Path
H=Path(__file__).resolve().parent;EV=H.parent
J=lambda p:json.load(open(p))
def axioms(l):
    r=J(H/f'PCQH_L{l}/receipt.json');out={}
    for a in r['print_axioms']:
        a=a.replace('\n','');m=re.match(r"'([^']+)' (.*)",a)
        out[m.group(1)]=m.group(2)
    return r,out
STD={'depends on axioms: [propext, Classical.choice, Quot.sound]','does not depend on any axioms'}
# verified runs: (label, run lean attempt, fresh run, gate ns, gate module, config)
VER=[('NFN_ExtractedGeometry_h1','008','PCQH_E001','NEW_GeometryActual','NFN_ExtractedGeometry','prov-p1h-20261109/PRVEq_NFN_ExtractedGeometry_h1.lean'),
     ('NFN_ExtractedGeometry_h2','011','PCQH_E003','NEW_GeometryActual','NFN_ExtractedGeometry','prov-p1h-20261109/PRVEq_NFN_ExtractedGeometry_h2.lean'),
     ('NJA_CountBody_h1','011','PCQH_E002','NJA_Multiproof','NJA_CountBody','prov-p1h-20261109/PRVEq_NJA_CountBody_h1.lean'),
     ('FIn_WeightsFuns_h1','011','PCQH_E003','FIn_WeightsExtract','FIn_WeightsFuns','prov-p1h-20261109/PRVEq_FIn_WeightsFuns_h1.lean'),
     ('RPz7_FIo_NativeFuns_h1','011','PCQH_E003','FIo_Native','RPz7_FIo_NativeFuns','prov-p1h-20261109/PRVEq_RPz7_FIo_NativeFuns_h1.lean')]
BIND={'NFN_ExtractedGeometry_h1':['ShrAmt shift-amount cast (PCQH_shr_prelude.lean): the OFF text calls Usize.wrapping_shr with an I32 amount; bridge = Rust `as u32`','M31.ZERO/ONE external constants bound to the gate values (NFN_prelude.lean); the binding equalities are PRVEq_const_bind (P2h L035/L037)']}
AL=J(EV/'prov-p2h-20261109/PCUH_ALL_STATUS.json')
eq=[];touched={}
for lab,l,run,gns,mod,f in VER:
    r,ax=axioms(l)
    for t,v in ax.items():
        m=re.match(r'PRVEq\.'+re.escape(lab)+r'\.(.*)',t)
        if not m: continue
        fresh=m.group(1);ok=v in STD
        defn=gns+'.'+fresh
        eq.append(dict(label=lab,theorem=t,fresh_name=fresh,definition=defn,gate_module=mod,fresh_run=run,lean_attempt='PCQH_L'+l,exit=r['exit_status'],axioms=v,standard_axioms_only=ok,file=f))
        touched[(mod,defn)]=eq[-1]
json.dump(dict(schema='PCQH_EQ_STATUS/1',target_established=False,records=eq),open(H/'PCQH_EQ_STATUS.json','w'),indent=1)
# merge into ALL_STATUS
new=copy.deepcopy(AL);new['schema']='PCQH_ALL_STATUS/1'
new['sources']=AL['sources']+['PCQH_EQ_STATUS.json (P1h: overflow-OFF fresh emissions PCQH_E001..E004)']
new['rule']=AL['rule']+'\n\nP1h: records whose gate body uses wrapping operators are compared against a fresh OFF emission (PCQH_E001 H07, PCQH_E002 H09, PCQH_E003 HF1). A P1h EQUALITY_PROVED record supersedes the earlier record for the same definition (listed in supersedes).'
sup=[];added=[]
for (mod,defn),e in touched.items():
    mm=new['modules'].get(mod)
    if mm is None: new['modules'][mod]=mm={}
    old=mm.get(defn)
    rec=dict(module=mod,definition=defn,status='EQUALITY_PROVED' if e['standard_axioms_only'] else 'OPEN',open_reason=None,theorem=e['theorem'],proving_file=e['file'],fresh_emission=e['fresh_run'],receipt=e['lean_attempt']+'/receipt.json',
      configuration='OFF',required_configuration='OFF (gate body uses wrapping operators) or checked-neutral',aeneas_tool='aeneas-b59d5188-extended',
      source_revision='frozen 4bb3b3f (fresh OFF emission) vs gate module source',decided_by='P1h',encoding_bridges=BIND.get(e['label']))
    if old:
        rec['supersedes']=[dict(status=old['status'],decided_by=old.get('decided_by'),theorem=old.get('theorem'),configuration=old.get('configuration'),open_reason=str(old.get('open_reason'))[:120])]
        sup.append(dict(module=mod,definition=defn,old_status=old['status'],old_decided_by=old.get('decided_by'),old_configuration=old.get('configuration')))
    else: added.append(dict(module=mod,definition=defn))
    mm[defn]=rec
new['p1h_superseded']=sup;new['p1h_added_records']=added
tot={}
nd=0
for mn,mv in new['modules'].items():
    for dn,r in mv.items(): tot[r['status']]=tot.get(r['status'],0)+1;nd+=1
new['totals']=tot;new['n_definitions']=nd;new['n_modules']=len(new['modules'])
json.dump(new,open(H/'PCQH_ALL_STATUS.json','w'),indent=1)
json.dump(dict(old_totals=AL['totals'],new_totals=tot,n_superseded=len(sup),n_added=len(added),
  upgraded_from_open=[s for s in sup if s['old_status']!='EQUALITY_PROVED' and s['old_status']!='RECEIPTED'],
  re_based_on_off=[s for s in sup if s['old_status'] in('EQUALITY_PROVED','RECEIPTED')]),open(H/'PCQH_STATUS_DIFF.json','w'),indent=1)
print(AL['totals'],'->',tot,len(sup),len(added))
