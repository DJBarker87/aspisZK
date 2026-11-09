#!/usr/bin/env python3
"""Writes PCQF_extract_specs.json (same schema as PCO_extract_specs.json / PCQ_extract_specs.json) for phase P1e.
Groups: SUP* = re-extraction of the six selections whose emissions P2c used, with aspis_core::field::P (and, for the
cost-probe selection, the five M31/QM31 items P2b found opaque) made transparent by --include; NEW* = frozen functions
behind P2b's 201 NO_FRESH_EMISSION definitions and P2c's S007/S008/S011 gaps. NO_FROZEN_COUNTERPART items are listed, not run."""
import json,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;EV=E.parent
FS='r0,pool-v1-kernel,pool-v1-pair-forest-packed-digest-selector-tensor-audit,pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-endpoint-selector-cache-audit,pool-v1-pair-forest-semantic-factor-audit,pool-v1-pair-forest-pattern-window-audit,pool-v1-pair-forest-copy-tag-dot-basis-audit,pool-v1-pair-forest-copy-finish-dot-basis-audit,pool-v1-pair-forest-packed-range-audit,pool-v1-pair-forest-active-mask-basis-audit'
STM=dict(crate='aspis-statement',manifest='crates/aspis-statement/Cargo.toml',features=FS)
CORE=dict(crate='aspis-core',manifest='crates/aspis-core/Cargo.toml',features='r0')
P='aspis_core::field::P'
specs=[]
def sup(sid,label,old_spec_file,newns,extra_include=()):
    o=json.loads((EV/old_spec_file).read_text());c=o['configuration']
    specs.append(dict(spec_id=sid,kind='frozen',label=label,crate=c['crate'],manifest=c['manifest'],features=c['features'],
        start_from=c['start_from'],include=[P]+list(extra_include),opaque=c['opaque'],namespace=newns,
        supersedes=dict(earlier_run=o['run'],earlier_spec=old_spec_file,earlier_include=c['include'],change='add --include '+', '.join([P]+list(extra_include))+'; start_from and opaque unchanged'),
        covers=o.get('covers'),basis='Same selection as the earlier run with the foreign constant made transparent so the emission declares a def, not an axiom.'))
sup('SUP1','S005a decode_digest_canonical/unwrap_fixed_slice','prov-p1c-20261109/PCQC_E002_spec.json','PCQF_aspis_statement_atomic_statement_a')
sup('SUP2','S009 pair_forest_accounts','prov-p1c-20261109/PCQC_E003_spec.json','PCQF_aspis_statement_pool_v1_pair_forest_accounts')
sup('SUP3','S014 spend','prov-p1c-20261109/PCQC_E004_spec.json','PCQF_aspis_statement_spend')
sup('SUP4','S015 cost-probe candidate query_values','prov-p1c-20261109/PCQC_E011_spec.json','PCQF_aspis_r1_cost_probe_candidate',
    ['aspis_core::field::_::ZERO','aspis_core::field::_::ONE','aspis_core::field::_::mul','aspis_core::field::reduce_u64','aspis_core::field::_::reduce_u64'])
sup('SUP5','S013 payment_relation','prov-p1a-20261109/PCQ_E039_spec.json','PCQF_aspis_statement_pool_v1_payment_relation')
sup('SUP6','S011 pair_terminal','prov-p1a-20261109/PCQ_E040_spec.json','PCQF_aspis_statement_pool_v1_pair_terminal')
def new(sid,label,cfg,roots,ns,mods,defs,syms=(),include=(),opaque=(),basis=None):
    specs.append(dict(spec_id=sid,kind='frozen',label=label,start_from=roots,include=list(include),opaque=list(opaque),namespace=ns,
        covers=dict(modules=mods,definitions=list(defs),rust_symbols=list(syms)),basis=basis or 'P1e: frozen functions behind P2b NO_FRESH_EMISSION definitions.',**cfg))
F='crate::field::'
new('NEW1','aspis-core field: M31/CM31/QM31 leaf arithmetic',CORE,[F+'reduce_u64',F+'_::reduce_u62',F+'_::reduce_u64',F+'_::ZERO',F+'_::ONE',F+'_::new',F+'_::from_m31',F+'_::add',F+'_::sub',F+'_::mul',F+'_::square',F+'_::mul_m31',F+'_::double',F+'_::from_cm31'],
    'PCQF_aspis_core_field_a',['RPu_FIq_Native01','RPu_FIq_Native02'],['field.reduce_u64','field.M31.reduce_u62','field.CM31.*','field.QM31.*'])
new('NEW2','aspis-core field: prepared multiplier, karatsuba, sum_products3_prepared, pack_base4, m31_dot',CORE,[F+'_::new',F+'_::mul',F+'qm31_from_karatsuba_channel_sums',F+'qm31_sum_products3_prepared',F+'qm31_pack_base4',F+'qm31_m31_dot'],
    'PCQF_aspis_core_field_b',['RPu_FIq_Native01','RPu_FIq_Native02','RPu_FIq_NativeTypes','RPv_PoseidonPreparedSum3Source','RPv_Qm31PackBase4Slice'],['field.PreparedQm31Multiplier.*','field.qm31_*'])
new('NEW3','aspis-core state_only_prefix r0 types',CORE,['crate::state_only_prefix::r0::Error','crate::state_only_prefix::r0::Challenges'],
    'PCQF_aspis_core_state_only_prefix',['RPu_FIq_NativeTypes'],['state_only_prefix.r0.Error','state_only_prefix.r0.Challenges'])
new('NEW4','aspis-statement constants: poseidon2, spend DOMAIN_*, pair_tree_profile capacity, pool_v1::format (S007)',STM,
    ['crate::poseidon2::INTERNAL','crate::poseidon2::POSEIDON2_WIDTH','crate::poseidon2::EXTERNAL_FINAL','crate::poseidon2::EXTERNAL_INITIAL','crate::poseidon2::RATE','crate::poseidon2::MERKLE_NODE_COMPRESSION_V3_TWEAK','crate::poseidon2::DIGEST_ELEMS',
     'crate::spend::DOMAIN_NOTE','crate::spend::DOMAIN_NULLIFIER','crate::spend::DOMAIN_OWNER_KEY','crate::pool_v1::pair_tree_profile::POOL_V1_PAIR_CAPACITY',
     'crate::pool_v1::format::POOL_V1_DIGEST_ENCODING_VERSION','crate::pool_v1::format::POOL_V1_TREE_DEPTH'],
    'PCQF_aspis_statement_consts',['RPu_FIq_Native03','RPu_FIq_Native04','RPu_FIq_Native06','RPu_FIq_Native07','RPu_FIq_Native08','RPu_FIq_Native10','RPu_FIq_Native11','AspisR1TerminalDecoder.Funs','NFY_Part043'],
    ['poseidon2.*','spend.DOMAIN_*','pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY','pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION','pool_v1.format.POOL_V1_TREE_DEPTH'])
new('NEW5','aspis-statement incremental_merkle PoolV1TreeError (S008)',STM,['crate::pool_v1::incremental_merkle::PoolV1TreeError'],
    'PCQF_aspis_statement_incremental_merkle',['AspisR1TerminalDecoder.Types','NFY_Part042'],['pool_v1.incremental_merkle.PoolV1TreeError'])
SOPN='crate::state_only_poseidon::'
new('NEW6','aspis-statement state_only_poseidon: Native04 closure',STM,[SOPN+n for n in ['extension_from_raw_limbs','extension_limbs','internal_linear_lazy','pow5','internal_round','interpolated_internal_pair']],
    'PCQF_aspis_statement_sop_a',['RPu_FIq_Native04','RPu_FIq_NativeTypes'],['state_only_poseidon.*'])
new('NEW7','aspis-statement state_only_poseidon: Native05 closure',STM,[SOPN+n for n in ['interpolate_three_constant_limb','interpolate_three_constant_columns','external_local_packed_raw','external_local_packed','external_linear_packed','full_round_packed']],
    'PCQF_aspis_statement_sop_b',['RPu_FIq_Native05','RPu_FIq_NativeTypes'],['state_only_poseidon.*'])
new('NEW8','aspis-statement state_only_poseidon: Native06/07 closure',STM,[SOPN+n for n in ['external_linear_lazy','full_round','interpolated_full_pair_packed','full_round_m31_constants_packed','full_round_m31_constants','leading_pair_packed','evaluate_state_only_poseidon_oracle_projected']],
    'PCQF_aspis_statement_sop_c',['RPu_FIq_Native06','RPu_FIq_Native07','RPu_FIq_NativeTypes'],['state_only_poseidon.*'])
SMT='crate::pool_v1::pair_forest_semantic_terminal::'
new('NEW9','aspis-statement pair_forest_semantic_terminal: public/selected/lane builders (Native03,07,08)',STM,[SMT+n for n in ['withdrawal_public','private_public','r0::_::semantic','selected_claim','copy_variant','scalar_lanes','lift_m31','add_digest_binding','empty_root','bounded_append_carry','public_digest_lanes','occupancy_lanes_literal','variant_expected_output']],
    'PCQF_aspis_statement_sem_a',['RPu_FIq_Native03','RPu_FIq_Native07','RPu_FIq_Native08','RPu_FIq_NativeTypes'],['pool_v1.pair_forest_semantic_terminal.*'])
new('NEW10','aspis-statement pair_forest_semantic_terminal: Native09/10 (add_* lanes, path, absorption)',STM,[SMT+n for n in ['add_preweighted','add_occupancy_lanes','reconstruct_10','add_value_lanes','path_lanes_literal','sum_high','add_path_lanes','absorption_lanes_literal','initial_variant_selectors','semantic_initial_and_absorption','add_schedule_lanes']],
    'PCQF_aspis_statement_sem_b',['RPu_FIq_Native09','RPu_FIq_Native10','RPu_FIq_NativeTypes'],['pool_v1.pair_forest_semantic_terminal.*'])
new('NEW11','aspis-statement pair_forest_semantic_terminal: Native11/14 (packed, selectors, transition, composition, terminal)',STM,[SMT+n for n in ['semantic_packed','poseidon_selectors','validate_transition','composition_parts','equality_value','terminal_parts','r0::_::terminal_qm31']],
    'PCQF_aspis_statement_sem_c',['RPu_FIq_Native11','RPu_FIq_Native14','RPu_FIq_NativeTypes'],['pool_v1.pair_forest_semantic_terminal.*'])
CPT='crate::pool_v1::pair_forest_copy_terminal::'
new('NEW12','aspis-statement pair_forest_copy_terminal',STM,[CPT+n for n in ['lift_m31','accumulate_endpoint','link_weight','copy_residual','_::row','pattern_values_literal','pattern_values','selector_mask_sum_16','_::active_literal','_::active','evaluate_with_selectors','_::expand','_::at_point','_::boxed_at_point']],
    'PCQF_aspis_statement_copy_terminal',['RPu_FIq_CopyPrefix','RPu_FIq_Native08','RPu_FIq_Native13','RPu_FIq_Native14','RPu_FIq_NativeTypes'],['pool_v1.pair_forest_copy_terminal.*'])
new('NEW13','aspis-statement pair_terminal gaps (S011): validate_verified_afterstate and encode_pool_v1_pair_verified_afterstate_v1 non-opaque',STM,
    ['crate::pool_v1::pair_terminal::validate_verified_afterstate','crate::pool_v1::pair_terminal::encode_pool_v1_pair_verified_afterstate_v1','core::option::_::ok_or'],
    'PCQF_aspis_statement_pair_terminal_b',['AspisR1TerminalDecoder.Funs'],['pool_v1.pair_terminal.validate_verified_afterstate','pool_v1.pair_terminal.validate_verified_afterstate_loop','pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1'],
    opaque=['crate::pool_v1::pair_tree_profile::validate_pool_v1_pair_live_snapshot_v1','crate::pool_v1::pair_tree_profile::encode_pool_v1_pair_live_snapshot_v1','crate::pool_v1::payment_relation::pool_v1_membership_root_v1','crate::atomic_statement::encode_digest_canonical'],
    basis='P2c S011 gap: the earlier S011 run made these two roots opaque (PCQ_E040 opacity), so no body was emitted.')
d=dict(schema=1,target_established=False,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
  note='P1e specs. include/opaque are applied exactly as listed; every run has overflow checks on.',specs=specs,
  no_frozen_counterpart=[
   dict(item='state_only_poseidon::external_linear_lazy_row (and ::closure)',modules=['RPu_FIq_Native06','RPu_FIq_NativeTypes','RPv_RawPoseidonExternalRowWrapperSlice','RPv_RowCallbackSlice'],status='NO_FROZEN_COUNTERPART',reason='probe-only helper: no item of that name in crates/aspis-statement/src/state_only_poseidon.rs at the frozen revision (P2b item_found_by_name false)'),
   dict(item='array_from_fn_copy (and _loop)',modules=['RPv_ArrayFromFnCopySlice'],status='NO_FROZEN_COUNTERPART',reason='probe-only helper: no such item in the frozen tree'),
   dict(item='core::num::u16::trailing_zeros (trailing_zeros_aux)',modules=['RPu_FIq_NativeExternal'],status='NO_FROZEN_COUNTERPART',reason='core library hand model of the gate; not an item of the frozen crates')])
(E/'PCQF_extract_specs.json').write_text(json.dumps(d,indent=1)+'\n');print(len(specs),'specs')
