import json,re
st=json.load(open('PCVD_STATUS.json'))
c=json.load(open('../prov-p3c-20261109/PCVC_REMAINING.json'))['items']
b=json.load(open('../prov-p3b-20261109/PCVB_REMAINING.json'))['items']
# proved sets: (module, definition-suffix)
proved=set()
for r in st['proved_records']:
    for t in r['theorems']:
        d=t.split('Eq.',1)[-1] if 'Eq.' in t else t
        proved.add((r['module'],d))
def is_proved(mod,d):
    if mod=='AspisR1WithdrawalCaller.Funs':
        d=d.split('payment_relation.')[-1]
        return (mod,d) in proved
    d2=d
    for pre in ['FIq_Native.','AspisR1PoseidonPreparedSum3Source.','AspisR1SelectedMaskProbe.','AspisR1WithdrawalCaller.','AspisR1WeightsFieldCurrent.','Port23PUSH.','AspisR1CurrentPreparedClaim.']:
        if d2.startswith(pre): d2=d2[len(pre):]
    cands={d2,d2.replace('aspis_core.',''),d2.replace('aspis_core.','',1)}
    return any((mod,x) in proved for x in cands)
FROMFN_DEP={('RPu_FIq_Native04',x) for x in ['state_only_poseidon.internal_linear_lazy','state_only_poseidon.internal_linear_lazy_loop1','state_only_poseidon.interpolated_internal_pair']}
FROMFN_DEP|={('RPu_FIq_Native05',x) for x in ['state_only_poseidon.external_linear_packed','state_only_poseidon.external_linear_packed_loop','state_only_poseidon.external_local_packed','state_only_poseidon.external_local_packed_raw','state_only_poseidon.external_local_packed_raw_loop0','state_only_poseidon.external_local_packed_raw_loop0_loop0','state_only_poseidon.full_round_packed']}
FROMFN_DEP|={('RPu_FIq_Native07',x) for x in ['state_only_poseidon.evaluate_state_only_poseidon_oracle_projected','state_only_poseidon.full_round_m31_constants_packed','state_only_poseidon.leading_pair_packed','state_only_poseidon.interpolated_full_pair_packed']}
FROMFN_DEP|={('RPu_FIq_Native09',P+x) for P in ['pool_v1.pair_forest_semantic_terminal.'] for x in ['add_value_lanes','add_preweighted','add_preweighted_loop','add_occupancy_lanes']}
FROMFN_DEP|={('RPu_FIq_Native10',P+x) for P in ['pool_v1.pair_forest_semantic_terminal.'] for x in ['absorption_lanes_literal','semantic_initial_and_absorption','add_path_lanes','add_schedule_lanes']}
FROMFN_DEP|={('RPu_FIq_Native11','pool_v1.pair_forest_semantic_terminal.semantic_packed')}
items={}
def key(m,d):
    d2=d
    for pre in ['FIq_Native.','AspisR1PoseidonPreparedSum3Source.','AspisR1SelectedMaskProbe.','AspisR1WithdrawalCaller.','AspisR1WeightsFieldCurrent.','Port23PUSH.','AspisR1CurrentPreparedClaim.','AspisR1TerminalDecoder.','AspisR1CurrentCaller.','NEW_GeometryActual.','AspisR1.FIp_NativeDots.','FIo_Native.','AspisR1.']:
        if d2.startswith(pre): d2=d2[len(pre):]
    return (m,d2.replace('aspis_core.','',1) if d2.startswith('aspis_core.') and '.field.' not in d2[:11] else d2)
for it in c: items.setdefault(key(it['module'],it['definition']),dict(module=it['module'],definition=it['definition'],origins=[]))['origins'].append('PCVC_REMAINING:'+it['p2g_class'])
for it in b: items.setdefault(key(it['module'],it['definition']),dict(module=it['module'],definition=it['definition'],origins=[]))['origins'].append('PCVB_REMAINING:'+it['p3b_status'])
NONFROZEN={'RPz7_FIo_NativeFuns','RPz7_FIp_NativeDots','AspisR1TerminalDecoder.Funs','NFN_ExtractedGeometry'}
out=[];closed=[]
for k,it in items.items():
    m,d=it['module'],it['definition']
    if is_proved(m,d) or (m,k[1]) in proved:
        closed.append(dict(module=m,definition=d,origins=it['origins'],result='PROVED_P3D')); continue
    o=' '.join(it['origins'])
    if m=='AspisR1TerminalDecoder.Funs' and 'pair_forest_accounts' in d:
        closed.append(dict(module=m,definition=d,origins=it['origins'],result='DISCHARGED_BY_P2F_REFINEMENT',note='loop-return refinement / plain equality proved in P2f PRVEq_TD_HP_P3f.lean (PCUF_L015) against transparent-P PCQF_E002; gate module non-frozen; not re-run here')); continue
    if (m,k[1]) in FROMFN_DEP or 'ARRAY_FROM_FN' in o:
        reason,cat='transitively depends on core.array.from_fn (an axiom in the original emission; gate uses array_from_fn_copy): hand model for P6, not provable here','HAND_MODEL_P6_FROM_FN'
    elif 'EXTERNAL_P_AXIOM' in o:
        reason,cat='fresh external aspis_core.field.P is an opaque axiom in the only emissions that contain the definition (PCQG_E005, PCQE_E008); the transparent-P emissions PCQF_E002..E006 do not contain pair_terminal.encode/validate or pair_tree_profile.digest_is_canonical; AND the gate module is non-frozen (PCXA) so it waits for P1g','EXTERNAL_P_NO_TRANSPARENT_EMISSION'
    elif m=='FIn_WeightsFuns' or 'CONFIG' in o:
        reason,cat='gate bodies use wrapping (overflow-OFF); every emission found is overflow-ON; no OFF emission covering this definition exists in the repository evidence (specs scanned: OVERFLOW_CHECKS=false none; PCQ_E415 covers only the fast_pairing dot items). Not a proof item; left as the brief says. Deployed wrapping is owned by R22.','CONFIG_MISMATCH_NO_OFF_EMISSION'
    elif 'BLOCKED_BY_CALLEE' in o:
        reason,cat='blocked by the CONFIG_MISMATCH callee (M31.add/sub/reduce_u64 in FIn_WeightsFuns)','CONFIG_MISMATCH_NO_OFF_EMISSION'
    elif m in NONFROZEN:
        reason,cat='gate module is one of the 26 non-frozen modules (PCVB_NONFROZEN_STATUS.json): waits for P1g, not equated here','NONFROZEN_WAIT_P1G'
    elif m=='CurrentCompactCallerModelV1':
        reason,cat='gate constant is a function of an Ops instance; equality needs a hypothesis on the Ops fields (HAND_ADAPTED)','HAND_ADAPTED_P6'
    elif m=='RPu_FIq_Native14':
        reason,cat='Native14 fresh section does not elaborate in 180 s (PCVC_L034/L042/L043 retired shape); excluded by the brief. The slice shape of PCVD_L031 (leave out the 200-line literal and take it as a parameter) may apply but was not tried','RETIRED_SHAPE_NOT_MINE'
    else:
        reason,cat='not examined','NOT_EXAMINED'
    out.append(dict(module=m,definition=d,origins=it['origins'],result='OPEN',category=cat,reason=reason))
# new obligations created by this phase
new=[dict(obligation='Native13: fresh constants.COPY_PATTERNS (200-line literal) = gate constants.COPY_PATTERNS (hand-compacted pattern00..13 in RPu_FIq_CopyPatterns)',status='NOT_ELABORATED (retired shape L034/L042/L043); every Native13 theorem using it is stated at the gate constant',consumer='PRVC.Eq.pattern_values_literal_loop1 / pattern_values_literal / pattern_values'),
     dict(obligation='cross-crate external constants bound to ok <gate constant>: aspis_core.field.QM31.ZERO, QM31.ONE, M31.ONE, state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS',status='INSTANTIATION (shim), not proved; the transparent aspis_core emissions PCQF_E007/E013 carry text-identical pure values for QM31.ZERO/ONE',consumer='every CONSTANT_BINDING row of PCVD_STATUS.json'),
     dict(obligation='parametric transports: W := WideExact / from_le_bytes (weights.field), ArrayIntoIter := MutAArray...into_iter (Port23PUSH), W := gate WideExact (trace.value)',status='consumer instantiation not proved (hand models for P6)',consumer='PRVD.Eq.weights.field, PRVC.Eq.verifier.update_residue_row/push, PRVD.Eq.trace.value'),
     dict(obligation='callee identification by name retained from P2g: aspis_core.field.M31.to_le_bytes (WithdrawalCaller), qm31_from_karatsuba_channel_sums in Native02, closure Insts',status='NAME-BOUND (as in P2g)',consumer='WithdrawalCaller encode_*, Native02 prepared')]
cnt={}
for o in out: cnt[o['category']]=cnt.get(o['category'],0)+1
json.dump(dict(schema='PCVD_REMAINING/1',target_established=False,universe=len(items),closed_in_P3d=len(closed),n_open=len(out),open_by_category=cnt,items=out,closed=closed,new_obligations=new),open('PCVD_REMAINING.json','w'),indent=1)
print(len(items),len(closed),len(out),cnt)
bl=[o for o in out if o['category']=='HAND_MODEL_P6_FROM_FN']
json.dump(dict(schema='PCVD_HAND_MODELS/1',target_established=False,
  hand_models=[dict(name='core.array.from_fn / array_from_fn_copy',why='axiom in the original-Aeneas emission; the gate carries array_from_fn_copy',blocked_definitions=[dict(module=o['module'],definition=o['definition']) for o in bl]),
               dict(name='compact.OFF_* (Ops-instance constants)',blocked_definitions=[dict(module=o['module'],definition=o['definition']) for o in out if o['category']=='HAND_ADAPTED_P6']),
               dict(name='external opaque types/functions abstracted as parameters',items=['aspis_core.field.wide_exact.WideExact and from_le_bytes (weights.field)','MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter (Port23PUSH ArrayIntoIter)','aspis_core.field.wide_exact.WideExact as the gate structure (trace.value)']),
               dict(name='cross-crate constant shims',items=['field.QM31.ZERO','field.QM31.ONE','field.M31.ONE','state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS'])]),open('PCVD_HAND_MODELS.json','w'),indent=1)
