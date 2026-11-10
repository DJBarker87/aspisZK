import json,glob,re,lzma,hashlib,os
from proved import proved
FROZEN='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
# ---- final successful attempt per file (latest exit 0 whose source hash matches the file on disk)
best={}
for r in sorted(glob.glob('PCVD_L[0-9][0-9][0-9]/receipt.json')):
    d=json.load(open(r))
    if d['exit_status']!=0: continue
    for f,h in d['source_hashes'].items():
        n=os.path.basename(f)
        if os.path.exists(n) and hashlib.sha256(open(n,'rb').read()).hexdigest()==h: best[n]=d
runs={}
for n,d in best.items():
    ax=proved(d['attempt'])[0]
    runs[n]=dict(attempt=d['attempt'],exit=d['exit_status'],wall_s=round(d['wall_seconds'],1),peak_rss_kib=d['peak_rss_kib'],swaps=d['swaps'],
        source_revision=d['source_revision'],source_tree_dirty=d['source_tree_dirty'],
        theorems={k:v for k,v in ax.items() if k.startswith(('PRVC.Eq.','PRVD.'))},
        all_axioms_standard=all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in ax.values()))
def T(file,*names,pre='PRVC.Eq.'):
    r=runs[file]; out=[]
    for n in names:
        k=n if n.startswith(('PRVC.','PRVD.')) else pre+n
        assert k in r['theorems'],(file,k)
        out.append(k)
    return out
P='pool_v1.pair_forest_semantic_terminal.'; Q='pool_v1.pair_forest_copy_terminal.'
rec=[]  # proved records
def add(module,definition,file,thms,cls,**kw):
    r=runs[file]
    rec.append(dict(module=module,definition=definition,result='PROVED_P3D',attempt=r['attempt'],file=file,theorems=thms,classification=cls,axioms='propext, Classical.choice, Quot.sound only (checked in receipt stdout)',**kw))
CB='CONSTANT_BINDING'
add('RPu_FIq_Native10','sum_high','PRVEq_RPu_FIq_Native10_P3.lean',T('PRVEq_RPu_FIq_Native10_P3.lean',P+'sum_high'),CB,instantiation='fresh external field.QM31.ZERO : Result QM31 read as ok FIq_Native.field.QM31.ZERO')
add('RPu_FIq_Native10','initial_variant_selectors','PRVEq_RPu_FIq_Native10_P3.lean',T('PRVEq_RPu_FIq_Native10_P3.lean',P+'initial_variant_selectors'),CB,instantiation='QM31.ZERO')
add('RPu_FIq_Native10','path_lanes_literal','PRVEq_RPu_FIq_Native10_P3.lean',T('PRVEq_RPu_FIq_Native10_P3.lean',P+'path_lanes_literal'),CB,instantiation='QM31.ZERO and QM31.ONE')
add('RPu_FIq_Native10','path_lanes_literal_loop','PRVEq_RPu_FIq_Native10_P3.lean',T('PRVEq_RPu_FIq_Native10_P3.lean',P+'path_lanes_literal_loop'),'HOISTED_CONSTANT_PARAMETER',statement='@Fresh.path_lanes_literal_loop (FIq_Native.field.QM31.ONE) = @Gate.path_lanes_literal_loop; the fresh loop carries a leading parameter q (the constant ONE hoisted by the tool); equality is claimed ONLY at q = QM31.ONE (the brief wrote ZERO; the source passes ONE).')
add('RPu_FIq_CopyPrefix','link_weight','PRVEq_RPu_FIq_CopyPrefix_P3.lean',T('PRVEq_RPu_FIq_CopyPrefix_P3.lean',Q+'link_weight'),CB,instantiation='field.M31.ONE : Result M31 read as ok FIq_Native.field.M31.ONE')
add('RPu_FIq_CopyPrefix','pair_forest_copy_terminal.lift_m31 (was NO_COMMON_LEAN_NAME)','PRVEq_RPu_FIq_CopyPrefix_P3.lean',T('PRVEq_RPu_FIq_CopyPrefix_P3.lean',Q+'lift_m31'),'SOURCE_SHAPE')
add('RPu_FIq_Native05','interpolate_three_constant_columns','PRVEq_RPu_FIq_Native05_P3.lean',T('PRVEq_RPu_FIq_Native05_P3.lean','state_only_poseidon.interpolate_three_constant_columns'),CB,instantiation='QM31.ZERO')
add('RPu_FIq_Native07','pool_v1.pair_forest_semantic_terminal.selected_claim (+ its constant COLUMNS_V1)','PRVEq_RPu_FIq_Native07_P3b.lean',T('PRVEq_RPu_FIq_Native07_P3b.lean',P+'POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1',P+'selected_claim'),CB,instantiation='state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS : Result Usize read as ok FIq_Native.<same>')
add('RPu_FIq_Native07','state_only_poseidon.interpolate_three_constant_columns (+ loop, limb)','PRVEq_RPu_FIq_Native07_P3b.lean',T('PRVEq_RPu_FIq_Native07_P3b.lean','state_only_poseidon.interpolate_three_constant_columns','state_only_poseidon.interpolate_three_constant_columns_loop'),CB,instantiation='QM31.ZERO',note='not a PCVC_REMAINING record; closed on the way')
add('RPu_FIq_Native11','poseidon_selectors (and sum_high)','PRVEq_RPu_FIq_Native11_P3.lean',T('PRVEq_RPu_FIq_Native11_P3.lean',P+'sum_high',P+'poseidon_selectors'),CB,instantiation='QM31.ZERO')
add('RPu_FIq_Native09','occupancy_lanes_literal (not a listed record; closed on the way)','PRVEq_RPu_FIq_Native09_P3.lean',T('PRVEq_RPu_FIq_Native09_P3.lean',P+'occupancy_lanes_literal'),CB,instantiation='QM31.ZERO and QM31.ONE')
n13='PRVEq_RPu_FIq_Native13_P3b.lean'
cp="instantiated with the gate constants.COPY_PATTERNS (fresh 200-line literal NOT elaborated: leading parameter COPY_PATTERNS := FIq_Native.pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS)"
add('RPu_FIq_Native13','pattern_values_literal_loop1',n13,T(n13,Q+'pattern_values_literal_loop1'),'HOISTED_CONSTANT_PARAMETER',statement='@Fresh.loop1 (COPY_PATTERNS_gate) (QM31.ZERO_gate) = @Gate.loop1; equality only at q = QM31.ZERO and the '+cp)
for d in ['pattern_values_literal_loop0','pattern_values_literal','pattern_values']:
    add('RPu_FIq_Native13',d,n13,T(n13,Q+d),'HOISTED_CONSTANT_PARAMETER' if d!='pattern_values_literal_loop0' else 'SOURCE_SHAPE',statement=('instantiation: '+cp) if d!='pattern_values_literal_loop0' else None)
for d in ['selector_mask_sum_16_loop','selector_mask_sum_16','Selectors.active_literal_loop','Selectors.active_literal','Selectors.active','constants.ACTIVE_ROW_MASKS']:
    add('RPu_FIq_Native13',d+' (beyond the brief: shape changed from the retired full-section compile)',n13,T(n13,Q+d),CB if d!='constants.ACTIVE_ROW_MASKS' else 'TEXT_IDENTICAL_CONSTANT',instantiation='QM31.ZERO/ONE' if d!='constants.ACTIVE_ROW_MASKS' else None)
add('RPu_FIq_Native02','field.qm31_sum_products3_prepared (+3 loops; was NO_COMMON_LEAN_NAME)','PRVEq_RPu_FIq_Native02_P3d.lean',T('PRVEq_RPu_FIq_Native02_P3d.lean','field.qm31_sum_products3_prepared','field.qm31_sum_products3_prepared_loop0','field.qm31_sum_products3_prepared_loop0_loop0','field.qm31_sum_products3_prepared_loop0_loop0_loop0'),'SOURCE_SHAPE',note='fresh text from PCQG_E001; callees (qm31_from_karatsuba_channel_sums) bound by name to the gate, as in P2g')
ps='PRVEq_RPv_PoseidonPreparedSum3Source_P3d.lean'
add('RPv_PoseidonPreparedSum3Source','field.qm31_from_karatsuba_channel_sums (+closure call)',ps,T(ps,'field.qm31_from_karatsuba_channel_sums','field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call'),'SOURCE_SHAPE',note='former HEARTBEAT_TIMEOUT: closed by simp-only on the proved callee equalities, then syntactic equality; no heartbeat option beyond the file default 1000000')
add('RPv_PoseidonPreparedSum3Source','field.qm31_sum_products3_prepared (+3 loops, + 9 callee equalities)',ps,T(ps,'field.qm31_sum_products3_prepared','field.qm31_sum_products3_prepared_loop0','field.qm31_sum_products3_prepared_loop0_loop0','field.qm31_sum_products3_prepared_loop0_loop0_loop0'),'SOURCE_SHAPE',note='gate callees live in AspisR1SelectedMaskProbe (the gate module opens it); namespace mismatch resolved by absolute gate names')
add('RPu_FIq_Native01','field.PreparedQm31Multiplier.mul (+closure call)','PRVEq_RPu_FIq_Native01_P3d.lean',T('PRVEq_RPu_FIq_Native01_P3d.lean','field.PreparedQm31Multiplier.mul','field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call'),'SOURCE_SHAPE',note='former HEARTBEAT_TIMEOUT: simp-only with the P2f callee equalities')
add('RPv_Qm31PackBase4Slice','field.qm31_pack_base4','PRVEq_RPv_Qm31PackBase4Slice_P3d.lean',T('PRVEq_RPv_Qm31PackBase4Slice_P3d.lean','field.qm31_pack_base4','field.reduce_u64','field.M31.reduce_u64','field.CM31.new','field.P','field.QM31.ZERO'),'NOMINAL',note='callee equalities added (fresh reduce_u64 = AspisR1SelectedMaskProbe.field.reduce_u64, both overflow-checked)')
add('RPv_RawPoseidonExtensionSlice','field.M31.reduce_u62','PRVEq_RPv_RawPoseidonExtensionSlice_P3d.lean',T('PRVEq_RPv_RawPoseidonExtensionSlice_P3d.lean','field.M31.reduce_u62','field.reduce_u64','field.P'),'NOMINAL')
wc='PRVEq_AspisR1WithdrawalCaller_Funs_P3d.lean'
add('AspisR1WithdrawalCaller.Funs','pool_v1.payment_relation.encode_common',wc,T(wc,'encode_common','atomic_statement.encode_digest_canonical','atomic_statement.encode_digest_canonical_loop','atomic_statement.encode_digest_canonical_loop.body'),'INSTANCE_TRANSPORT',transport='fresh cross-crate external atomic_statement.encode_digest_canonical replaced by the transparent PCQE_E002 emission text (aspis_statement::atomic_statement) and proved equal to the gate local helper encode_digest_canonical (body, loop, wrapper).')
add('AspisR1WithdrawalCaller.Funs','pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1',wc,T(wc,'encode_pool_v1_withdrawal_public_v1'),'INSTANCE_TRANSPORT')
add('AspisR1WithdrawalCaller.Funs','pool_v1.payment_relation.validate_common / validate_pool_v1_withdrawal_public_v1 (re-verified; first proved in PCVC_L046)',wc,T(wc,'validate_common','validate_pool_v1_withdrawal_public_v1'),'SOURCE_SHAPE',note='P3b class SEMANTIC corrected to SOURCE_SHAPE by P3c: only the constant path differs; values equal')
add('WeightsFieldExplicitDecoder','weights.field','PRVEq_WeightsFieldExplicitDecoder_P3d.lean',['PRVD.Eq.weights.field'],'INSTANCE_TRANSPORT_PARAMETRIC',statement='for all types W and decoders d: fresh weights.field[W,d] = gate weights.field W d; binding W := aspis_core.field.wide_exact.WideExact, d := its from_le_bytes is the consumer instantiation and is NOT proved (opaque externals in the fresh emission).')
add('Port23PUSH_Source','verifier.update_residue_row / verifier.BatchedWeights.push','PRVEq_Port23PUSH_Source_P3d.lean',T('PRVEq_Port23PUSH_Source_P3d.lean','verifier.update_residue_row','verifier.BatchedWeights.push'),'INSTANCE_TRANSPORT_PARAMETRIC',statement='for every ai : ArrayIntoIter: fresh[with MutAArray...into_iter := ai] = gate ai.  The gate declares ArrayIntoIter an uninterpreted external ABI; that the real MutAArray...into_iter satisfies the consumer assumptions is NOT proved here (hand model, P6).')
add('CurrentClaimSumModel','trace.value','PRVEq_CurrentClaimSumModel_trace_P3d.lean',['PRVD.Eq.trace.value'],'INSTANCE_TRANSPORT_PARAMETRIC',statement='fresh trace.value[W := gate aspis_core.field.WideExact] = gate trace.value; the body ignores x.  The identification of the external type with the gate structure is NOT proved here.')
add('AspisR1BatchedWeightsExtraction.Funs','aspis_core.field.M31.reduce_u64','PRVEq_AspisR1BatchedWeightsExtraction_Funs_P3d.lean',['PRVC.Eq.field.M31.reduce_u64'],'NOMINAL',note='name-map alias: fresh crate-relative field.* vs gate aspis_core.field.*; callee reduce_u64 by the P2g theorem')
add('(generic)','constant-binding lemmas','PRVD_ConstBind.lean',['PRVD.const_bind','PRVD.const_bind_of_eq','PRVD.hoisted_param_eq','PRVD.const_bind_unique'],'GENERIC_LEMMA')
for m in ['PRVEq_RPu_FIq_Native10_P3.lean']: pass
json.dump(dict(schema='PCVD_STATUS/1',target_established=False,frozen_source=FROZEN,
  note='Every theorem below compiled in the cited attempt with exit 0; #print axioms output is propext/Classical.choice/Quot.sound only (or none).  Statements are fresh = gate against compiled gate constants.  CONSTANT_BINDING results are equalities in which the fresh cross-crate external constant is INSTANTIATED to ok <gate constant> (shim definitions inside the fresh namespace); the binding is not proved by these theorems.  PARAMETRIC results abstract an opaque external of the fresh emission as a parameter.  No sorry, axiom, native_decide, raised heartbeat or trust row was added.',
  runs=runs,proved_records=rec,counts=dict(records=len(rec),files=len(runs))),open('PCVD_STATUS.json','w'),indent=1)
print(len(rec),len(runs))
