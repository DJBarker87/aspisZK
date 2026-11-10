#!/usr/bin/env python3
"""PCUI_remaining.py: PCUI_REMAINING.json (what is still open in scope, by class), PCUI_HAND_MODELS.json (ShrAmt prelude use), PCUI_CLASSIFICATIONS bookkeeping input."""
import json,os,re,sys,collections
sys.dont_write_bytecode=True
H=os.path.dirname(os.path.abspath(__file__));EV=os.path.dirname(H)
sys.path.insert(0,EV+'/prov-p2h-20261109');import PCUH_gen_equalities as G
P=json.load(open(EV+'/prov-p6c-20261109/PCXB_PROVENANCE.json'));ST=json.load(open(H+'/PCUI_STATUS.json'))['records']
done={(c['module'],c['definition']) for c in ST}
ns=json.load(open(EV+'/prov-p6c-20261109/PCXB_NOSOURCE.json'));so=json.load(open(EV+'/prov-p6c-20261109/PCXB_SECOND_TIER_OPEN.json'))
cut=set()
for k in list(ns['modules'])+list(so['modules']): cut.add(k if isinstance(k,str) else k.get('module'))
TB=json.load(open(H+'/PCUI_TYPEBASIS_CANDIDATES.json'));BB=json.load(open(H+'/PCUI_BASIS_CANDIDATES.json'))
rem=[];cls=collections.Counter()
for mn,m in P['modules'].items():
    for dn,df in m['definitions'].items():
        if not (df['in_splitB_cone'] and df['status']=='OPEN') or (mn,dn) in done: continue
        oc=df.get('open_class');r=df.get('open_reason') or ''
        if oc=='NO_FRESH_EMISSION' or r.startswith('no Lean equality'): continue   # out of this job's scope (325 + 40)
        if mn in cut: k='SKIP_CUT_MODULE_HELD_FOR_OWNER'
        elif 'HAND_ADAPTED' in r or 'HAND_MODEL_P6_FROM_FN' in r or 'FROM_FN' in r: k='SKIP_HAND_MODEL_OR_HAND_ADAPTED'
        elif 'RETIRED_SHAPE' in r or 'Native14' in mn: k='SKIP_RETIRED_SHAPE_NATIVE14'
        elif 'NO_FROZEN' in r: k='SKIP_NO_FROZEN_COUNTERPART'
        elif oc=='WRONG_BASIS':
            k='WB_NO_IDENTICAL_EMISSION_NEEDS_EXTRACTION'
        elif r.startswith(('TEXT_IDENTICAL_ONLY','TEXT_ONLY','TEXT_DIFFERS')): k='TYPE_STRUCTURE_FIELD_TRANSPORT_OR_TEXT_DIFF'
        elif r.startswith('FAILED') or 'did not elaborate' in r or r.startswith(('FRESH_NOT','OPEN_')): k='FAILED_FRESH_OR_PROOF'
        elif r.startswith('NOT_COVERED'): k='NOT_COVERED_NO_TEXT_IDENTICAL_RECEIPTED_EMISSION'
        else: k='OTHER'
        cls[k]+=1;rem.append(dict(module=mn,definition=dn,cls=k,reason=r[:140],open_class=oc))
json.dump(dict(schema='PCUI_REMAINING/1',target_established=False,counts=dict(cls),items=rem),open(H+'/PCUI_REMAINING.json','w'),indent=1)
print(dict(cls))
# ShrAmt use
txt=open(H+'/PRVEq_NJS_Extract_Funs_i2.lean').read()
bl=[b for b in G.parse_blocks(txt) if b['kind']=='decl']
names=[b['name'] for b in bl];direct={b['name'] for b in bl if re.search(r'Std\.U64\.wrapping_sh[lr]',b['body']) and 'ShrAmt' not in b['body'][:80] and not b['name'].startswith('Std.U64')}
dep=set(direct);ch=True
while ch:
    ch=False
    for b in bl:
        if b['name'] not in dep and set(G.lean_ident_tokens(b['body']))&dep: dep.add(b['name']);ch=True
used=[d for d in done if d[0]=='NJS_Extract.Funs' and d[1].split('NJS_Extract.',1)[-1] in dep]
json.dump(dict(schema='PCUI_HAND_MODELS/1',entries=[dict(name='ShrAmt',file='prov-p2i-20261110/inputs/prelude_shramt_u64.lean',kind='encoding bridge (hand model)',scope='U64 wrapping_shl/wrapping_shr with an I32/Usize shift amount; overflow-checks-OFF only',verification='evidence/shramt-20261110/NPE_SHRAMT_CHECK.md (OFF only; never for checked shifts with amounts wider than 32 bits)',used_in='PRVEq_NJS_Extract_Funs_i2.lean (pass fresh = NMH_E010 NJS_Extract, OFF default environment)',credited_definitions_depending_on_it=sorted(used),fresh_declarations_depending=sorted(dep)),
  dict(name='gate externals as variables',note='NJS_Extract.Funs / NMP_prepare.Funs gate declarations that depend on the NJS_call_k / NMP_call_k variables have no text-identical emission (the fresh emission refers to the concrete external); they are NOT credited here (parametric transport, CONDITIONAL_ON_BINDING at best).')]),open(H+'/PCUI_HAND_MODELS.json','w'),indent=1)
print('shramt-dependent credited',len(used))
