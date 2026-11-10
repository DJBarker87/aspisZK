#!/usr/bin/env python3
"""PCQI_ingest.py: receipts -> PCQI_PROVED.json and PCQI_ALL_STATUS.json (PCUJ_ALL_STATUS.json with the PCQI records merged).
A definition is credited only if its scope exited 0, the theorem (or Types equivalence def) named for it appears in the scope's
#print axioms output with standard axioms only, and it is a declared target below."""
import json,re,os,sys,copy
sys.dont_write_bytecode=True
STD={'propext','Classical.choice','Quot.sound'}
EV='..'
def axioms(a):
    p=f'PCQI_{a}/receipt.json'
    if not os.path.exists(p):return None,{}
    r=json.load(open(p));out={}
    for x in r['print_axioms']:
        x=re.sub(r'\s+',' ',x);m=re.match(r"'([^']+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)",x)
        out[m.group(1)]={s.strip() for s in (m.group(2) or '').split(',') if s.strip()}
    return r,out
E1='prov-p1i-20261110/PCQI_E001_emitted/raw/PCQI_wide_mul';E2='prov-p1i-20261110/PCQI_E002_emitted/raw/PCQI_wide_ops'
E6='prov-p1i-20261110/PCQI_E006_emitted/raw/PCQI_field_inv';E7='prov-p1i-20261110/PCQI_E007_emitted/raw/PCQI_h07on'
J4='prov-p2j-20261110/PCUJ_E004_emitted/raw/NMH_field_decode';J5='prov-p2j-20261110/PCUJ_E005_emitted/raw/NMH_wide_decode'
D24='prov-p1g-20261109/PCQD_E024_emitted/raw/PCQD_d15';D18='prov-p1g-20261109/PCQD_E018_emitted/raw/PCQD_d09';D36='prov-p1g-20261109/PCQD_E036_emitted/raw/PCQD_d03a'
# (scope, file, theorem prefix, gate module, gate def prefix, [(fresh name, theorem suffix or None)], fresh dir, emission run, tool, kind, note)
def T(names,suf=''): return [(n,n+suf) for n in names]
V8=['field.M31.inv','field.square_n','field.square_n_loop','field.square_n_loop.body']
CR=[
('L004','PRVEq_CurrentWideMulCanonical_j4.lean','PRVEq.CurrentWideMulCanonical_j4.','CurrentWideMulCanonical','AspisR1CurrentWideMul.',T(['field.QM31.sub','field.wide_exact.mul_u','field.wide_exact.WideExact.mul']),E1,'PCQI_E001','extended','FUNCTION_EQUALITY','callees equated to the compiled AspisR1Qm31ArithmeticProbe constants the gate abbreviates; Types basis: PCQI_L005'),
('L006','PRVEq_AspisR1CurrentWide_Funs_j1.lean','PRVEq.AspisR1CurrentWide.Funs_j1.','AspisR1CurrentWide.Funs','AspisR1CurrentWide.',T(['field.wide_exact.WideExact.add','field.wide_exact.WideExact.sub','field.wide_exact.WideExact.mul','field.wide_exact.WideExact.mul_m31','field.wide_exact.mul_u']),E2,'PCQI_E002','extended','FUNCTION_EQUALITY',''),
('L007','PRVEq_AspisC2HostEmbedding_Funs_j1.lean','PRVEq.AspisC2HostEmbedding.Funs_j1.','AspisC2HostEmbedding.Funs','AspisC2HostEmbedding.',T(['field.wide_exact.WideExact.from_qm31','field.wide_exact.canonical_qm31']),E2,'PCQI_E002','extended','FUNCTION_EQUALITY',''),
('L008','PRVEq_AspisC2HostEmbedding_Types_t1.lean','PRVEq.AspisC2HostEmbedding.Types_t1.','AspisC2HostEmbedding.Types','AspisC2HostEmbedding.',T(['field.wide_exact.canonical_qm31.closure']),E2,'PCQI_E002','extended','TYPES_EQUALITY','closure type is Unit; no arithmetic'),
('L009','PRVEq_RPv_EqualityValueSlice_j1.lean','PRVEq.RPv_EqualityValueSlice_j1.','RPv_EqualityValueSlice','AspisR1SelectedMaskProbe.',T(['field.QM31.sub']),E1,'PCQI_E001','extended','FUNCTION_EQUALITY','callee CM31.sub/M31.sub equated to the SelectedMaskProbe Funs constants'),
('L010','PRVEq_RPz7_FIp_DotDecode_j1.lean','PRVEq.RPz7_FIp_DotDecode_j1.','RPz7_FIp_DotDecode','AspisR1.FIp_DotDecode.',T(['field.M31.from_le_bytes','field.CM31.from_le_bytes','field.QM31.from_le_bytes']),J4,'PCUJ_E004 (P2j, reused, ON)','extended','FUNCTION_EQUALITY','externals Option.branch / from_residual resolve to the gate hand definitions; types via the FIo_Native Types records'),
('L011','PRVEq_R1CandidateFieldParsers_j1.lean','PRVEq.R1CandidateFieldParsers_j1.','R1CandidateFieldParsers','AspisR1CandidateParser.',T(['field.M31.from_le_bytes','field.CM31.from_le_bytes','field.QM31.from_le_bytes']),J4,'PCUJ_E004 (P2j, reused, ON)','extended','FUNCTION_EQUALITY','externals Option.branch / from_residual resolve to the gate hand definitions'),
('L013','PRVEq_R1CandidateWideParserSource_j2.lean','PRVEq.R1CandidateWideParserSource_j2.','R1CandidateWideParserSource','AspisR1CandidateParser.',T(['field.wide_exact.WideExact.BYTE_LEN']),J5,'PCUJ_E005 (P2j, reused, ON)','extended','FUNCTION_EQUALITY','constant only; from_le_bytes has a different body (see PCQI_CLASSIFICATIONS.json PCQI-C6)'),
('L014','PRVEq_AspisV8R19_GuardedFieldSlice_j1.lean','PRVEq.AspisV8R19.GuardedFieldSlice_j1.','AspisV8R19.GuardedFieldSlice','AspisR64Field.',T(V8),E6,'PCQI_E006','extended','FUNCTION_EQUALITY','M31.mul via P3b fast_chain lemma (PCVB_M31, copied); inv/square_n by delta+callee rewrite'),
('L015','PRVEq_AspisV8R19_ComplexFieldSlice_j1.lean','PRVEq.AspisV8R19.ComplexFieldSlice_j1.','AspisV8R19.ComplexFieldSlice','AspisR65Field.',T(V8),E6,'PCQI_E006','extended','FUNCTION_EQUALITY','as L014'),
('L016','PRVEq_AspisV8R19_QuarticFieldSlice_j1.lean','PRVEq.AspisV8R19.QuarticFieldSlice_j1.','AspisV8R19.QuarticFieldSlice','AspisR66Field.',T(V8),E6,'PCQI_E006','extended','FUNCTION_EQUALITY','as L014; r23_product_u32_bounded has no frozen counterpart and is not covered'),
('L017','PRVEq_Stage2ContinuationTypes_t1.lean','PRVEq.Stage2ContinuationTypes_t1.','Stage2ContinuationTypes','AspisR1Stage2.',T(['verifier.QueryGeometry.for_range.closure','verifier.QueryGeometry.for_range.closure_1','verifier.QueryGeometry.for_range.closure_2','verifier.QueryGeometry.for_range.closure_3','verifier.QueryGeometry.for_range.closure_4','verifier.QueryGeometry.for_range.closure_4.closure']),E7,'PCQI_E007','extended','TYPES_EQUALITY','closure types; ON counterpart of the OFF PCQH_E001 shape'),
('L018','PRVEq_RPu_FIq_Native01_j1.lean','PRVEq.RPu_FIq_Native01_j1.','RPu_FIq_Native01','FIq_Native.',T(['field.M31.Insts.CoreCmpPartialEqM31.eq']),D24,'PCQD_E024 (P1g, reused, ON)','extended','FUNCTION_EQUALITY',''),
('L019','PRVEq_CurrentWideEqSemanticV7_j1.lean','PRVEq.CurrentWideEqSemanticV7_j1.','CurrentWideEqSemanticV7','AspisR1CurrentWide.',T(['field.M31.Insts.CoreCmpPartialEqM31.eq','field.CM31.Insts.CoreCmpPartialEqCM31.eq']),D24,'PCQD_E024 (P1g, reused, ON)','extended','FUNCTION_EQUALITY','QM31 and WideExact eq not covered (no ON emission)'),
('L020','PRVEq_NJA_Multiproof_Types_t1.lean','PRVEq.NJA_Multiproof.Types_t1.','NJA_Multiproof.Types','NJA_Multiproof.',T(['multiproof.well_formed.closure','multiproof.well_formed.closure_1']),D18,'PCQD_E018 (P1g, reused, ON)','extended','TYPES_EQUALITY','closure types'),
('L023','PRVEq_AspisR1DecodeKFullV10_Types_t1.lean','PRVEq.AspisR1DecodeKFullV10.Types_t1.','AspisR1DecodeKFullV10.Types','AspisR1DecodeKFullV10.',[('r1_wire.Error','r1_wire.Error.equiv'),('r1_wire.ValidatedRecord','r1_wire.ValidatedRecord.equiv')],D36,'PCQD_E036 (P1g, reused, ON)','extended','TYPES_EQUIV','Equiv isomorphism of Types declarations'),
('L024','PRVEq_ClaimsUnrolledParentTypes_t1.lean','PRVEq.ClaimsUnrolledParentTypes_t1.','ClaimsUnrolledParentTypes','AspisR1ClaimsUnrolledParent.',[('r1_wire.Prefix','r1_wire.Prefix.equiv'),('r1_wire.ValidatedRecord','r1_wire.ValidatedRecord.equiv')],D36,'PCQD_E036 (P1g, reused, ON)','extended','TYPES_EQUIV','Equiv isomorphism of Types declarations'),
('L025','PRVEq_AspisR1PublicPreparation_Types_t1.lean','PRVEq.AspisR1PublicPreparation.Types_t1.','AspisR1PublicPreparation.Types','AspisR1PublicPreparation.',[('r1_wire.Error','r1_wire.Error.equiv')],D36,'PCQD_E036 (P1g, reused, ON)','extended','TYPES_EQUIV','Equiv isomorphism of Types declarations'),
]
# L023..: tuple arity fix (lists passed above for the target list)
proved={}
for row in CR:
    sc,f,pre,mod,gp,tg,fd,run,tool,kind,note=row
    r,ax=axioms(sc)
    if r is None:continue
    if r['exit_status']!=0:continue
    for fn,suf in tg:
        th=pre+suf
        if th not in ax or (ax[th]-STD):print('NOT CREDITED',sc,th,ax.get(th));continue
        proved[gp+fn]=dict(theorem=th,module=mod,receipt=f'prov-p1i-20261110/PCQI_{sc}/receipt.json',proving_file='prov-p1i-20261110/'+f,config='ON',fresh_dir=fd,emission_run=run,aeneas_tool=tool,kind=kind,note=note)
json.dump(proved,open('PCQI_PROVED.json','w'),indent=1)
print(len(proved),'credited definitions')
# merge into PCUJ_ALL_STATUS
a=json.load(open('../prov-p2j-20261110/PCUJ_ALL_STATUS.json'));sup=[];miss=[]
for d,v in proved.items():
    m=v['module'];rec=a['modules'].get(m,{}).get(d)
    if rec is None:miss.append((m,d));continue
    old=dict(status=rec['status'],open_reason=rec.get('open_reason'),theorem=rec.get('theorem'))
    sup.append(dict(module=m,definition=d,was=rec['status'],was_reason=(rec.get('open_reason') or '')[:120]))
    rec.update(status='EQUALITY_PROVED',open_reason=None,theorem=v['theorem'],proving_file=v['proving_file'],fresh_emission=v['fresh_dir'],receipt=v['receipt'],configuration='ON',aeneas_tool=v['aeneas_tool'],decided_by='P1i',pcqi_basis_note=v['kind']+': '+v['note'])
    rec.setdefault('supersedes',[]).append(dict(source='PCUJ',**old))
tot={}
for m in a['modules'].values():
    for r in m.values():tot[r['status']]=tot.get(r['status'],0)+1
a['totals']=tot;a['schema']='PCQI_ALL_STATUS/1'
a['pcqi_superseded']=sup;a['pcqi_unmatched']=miss
a['pcqi_note']='PCUJ_ALL_STATUS.json with the P1i (PCQI_) records merged: OPEN to EQUALITY_PROVED where a PCQI_ scope exited 0 with standard axioms only. See PCQI_PROVED.json.'
json.dump(a,open('PCQI_ALL_STATUS.json','w'),indent=1)
print('totals',tot,'unmatched',miss)
