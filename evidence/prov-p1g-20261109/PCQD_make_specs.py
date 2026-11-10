#!/usr/bin/env python3
"""Build PCQD_extract_specs.json: one spec per frozen extraction group for the 113 gate definitions of PCVB_NEED_EXTRACTION.json
that PCQD_cover.py did not find in an existing def-kind emission. Tool: extended Aeneas first (lead decision)."""
import json,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
CP='private-leaf-salts,optimized-terminal,program-build'
C={'prog':dict(crate='aspis-r1-cost-probe-program',manifest='programs/r1-cost-probe/Cargo.toml',features='pool-adapter,private-leaf-salts'),
   'cp':dict(crate='aspis-r1-cost-probe',manifest='crates/aspis-r1-cost-probe/Cargo.toml',features=CP),
   'st':dict(crate='aspis-statement',manifest='crates/aspis-statement/Cargo.toml',features='r0,pool-v1-kernel'),
   'core':dict(crate='aspis-core',manifest='crates/aspis-core/Cargo.toml',features='r0')}
P=['aspis_core::field::P']
S=[]
def add(sid,c,label,roots,opaque=(),include=P,modules=(),basis='',tool='extended'):
    s=dict(spec_id=sid,kind='frozen',label=label,start_from=list(roots),include=list(include),opaque=list(opaque),namespace='PCQD_'+sid.lower(),aeneas_tool=tool,covers=dict(modules=list(modules)),basis=basis,**C[c]);S.append(s)
OPQ_PROG=['aspis_statement::pool_v1::pair_forest_terminal::validate_pool_v1_pair_forest_terminal_statement_v1']
add('D01','prog','AdapterRw: first_decoded, observer, owned require_* helpers, readonly_buffer_meta_ok, OwnedAccount::data_len',
 ['crate::first_decoded','crate::observer','crate::r1_pool_adapter::owned::require_distinct_accounts','crate::r1_pool_adapter::owned::require_readonly_buffer','crate::r1_pool_adapter::owned::require_verifier_checkpoint','crate::r1_pool_adapter::owned::require_zero','crate::r1_pool_adapter::readonly_buffer_meta_ok','crate::r1_pool_adapter::owned::_::data_len'],
 opaque=['aspis_r1_cost_probe::verifier::tx1','crate::error'],modules=['AdapterRwModel'],basis='Callees of first_decoded outside the gate definitions (verifier::tx1, error) opaque as P1c did for crate-level callees.')
add('D02','prog','AdapterReconstruct: asq8_common, reconstruct_asq8_statement, transfer/withdrawal_statement_box',
 ['crate::r1_pool_adapter::asq8_common','crate::r1_pool_adapter::reconstruct_asq8_statement','crate::r1_pool_adapter::transfer_statement_box','crate::r1_pool_adapter::withdrawal_statement_box'],
 opaque=OPQ_PROG,modules=['AspisR1AdapterReconstruct.Funs','AspisR1AdapterReconstruct.Types'],basis='validate_pool_v1_pair_forest_terminal_statement_v1 opaque as in PCQC_E023.')
add('D03','cp','r1_wire: ValidatedRecord decode_k/payload, row_shape, CLAIMS, LANES, SemanticTranscript, Error',
 ['crate::r1_wire::_::decode_k','crate::r1_wire::_::payload','crate::r1_wire::row_shape','crate::r1_wire::CLAIMS','crate::r1_wire::LANES','crate::r1_wire::SemanticTranscript','crate::r1_wire::Error'],
 modules=['AspisR1DecodeKFullV10.Funs','AspisS1NativeCompactModelV1','CurrentCompactCallerTypesV1'])
add('D04','cp','compact: SEMANTIC_ROWS, compact_row, expand_semantic',
 ['crate::compact::SEMANTIC_ROWS','crate::compact::compact_row','crate::compact::expand_semantic'],modules=['S1NativeCompactModelV1'])
add('D05','cp','r1_semantic: Verified type, claims, verifier::View',
 ['crate::r1_semantic::claims','crate::r1_semantic::Verified','crate::verifier::View'],modules=['ClaimsUnrolledParentSource','NJT_ClaimsRef_Funs','CurrentCompactCallerTypesV1'])
add('D06','cp','fast_domain: TABLE_A, TABLE_B, table_value, fibre_point, line_node',
 ['crate::fast_domain::TABLE_A','crate::fast_domain::TABLE_B','crate::fast_domain::table_value','crate::fast_domain::fibre_point','crate::fast_domain::line_node'],modules=['NFN_ExtractedGeometry'])
add('D07','cp','verifier: QueryGeometry::for_range, batch_prefix_products',
 ['crate::verifier::_::for_range','crate::verifier::batch_prefix_products'],modules=['NFN_ExtractedGeometry','Port3_NativeGeometryBody','Port4C_NativePrefix'])
add('D08','cp','NGN: transport Variant::folds, Prepared::new',
 ['crate::transport::_::folds','crate::verifier::_::new'],modules=['NGN_Emitted'])
add('D09','cp','multiproof::node_count',['crate::multiproof::node_count'],modules=['NJA_CountBody'])
add('D10','cp','candidate: batch_merkle, batch_merkle_values, batch_tree, query_loop',
 ['crate::verifier::candidate::batch_merkle','crate::verifier::candidate::batch_merkle_values','crate::verifier::candidate::batch_tree','crate::verifier::candidate::query_loop'],modules=['Port3_NativeBatchBody','Port3_NativeQueryBody'])
add('D11','cp','verifier: BatchedWeights::new, read_checkpoint_weights, validate_checkpoint_queries, candidate::prepare',
 ['crate::verifier::_::new','crate::verifier::read_checkpoint_weights','crate::verifier::candidate::prepare'],modules=['Port3_NativePendingBody','Port5Q2_ReaderWeights','CurrentCompactCallerTypesV1'])
add('D12','st','pair_forest_terminal boxed decoders and MASTER_OFFSET',
 ['crate::pool_v1::pair_forest_terminal::decode_lane_transition_boxed_v1','crate::pool_v1::pair_forest_terminal::decode_terminal_common_boxed_v1','crate::pool_v1::pair_forest_terminal::decode_transfer_statement_boxed_v1','crate::pool_v1::pair_forest_terminal::decode_withdrawal_statement_boxed_v1','crate::pool_v1::pair_forest_terminal::MASTER_OFFSET'],modules=['AspisR1TerminalDecoder.Funs'])
add('D13','st','pair_tree_profile boxed decoders, live snapshot encode/validate',
 ['crate::pool_v1::pair_tree_profile::decode_pair_afterstate_boxed_v1','crate::pool_v1::pair_tree_profile::decode_pair_live_snapshot_boxed_v1','crate::pool_v1::pair_tree_profile::decode_pool_v1_pair_late_public_statement_boxed_v1','crate::pool_v1::pair_tree_profile::encode_pool_v1_pair_live_snapshot_v1','crate::pool_v1::pair_tree_profile::validate_pool_v1_pair_live_snapshot_v1'],modules=['AspisR1TerminalDecoder.Funs'])
add('D14','st','asq8_payment_reference::encode_common, asq8_reference_envelope',
 ['crate::pool_v1::pair_forest_terminal::asq8_payment_reference::encode_common','crate::pool_v1::pair_forest_terminal::asq8_reference_envelope'],modules=['NFY_Part043'])
add('D15','core','circle: secure_circle_point_from_parameter, secure_ood_circle_point_from_parameter, CirclePointError',
 ['crate::circle::secure_circle_point_from_parameter','crate::circle::secure_ood_circle_point_from_parameter','crate::circle::CirclePointError'],include=[],modules=['AspisR72Sampler.Funs','AspisR72Sampler.Types'])
add('D16','core','field: M31::inv, CM31::inv/inv_with, QM31::try_inv, square_n, eq instances',
 ['crate::field::_::inv','crate::field::_::inv_with','crate::field::_::try_inv','crate::field::square_n','crate::field::_::eq'],include=[],modules=['AspisR72Sampler.Funs'])
add('D17','core','r0::transport::order (priority: last unexamined SEMANTIC item)',['crate::r0::transport::order','core::option::_::ok_or'],include=[],modules=['FIo_Native'])
add('D01a','prog','AdapterRw split a: all D01 roots except require_distinct_accounts',
 ['crate::first_decoded','crate::observer','crate::r1_pool_adapter::owned::require_readonly_buffer','crate::r1_pool_adapter::owned::require_verifier_checkpoint','crate::r1_pool_adapter::owned::require_zero','crate::r1_pool_adapter::readonly_buffer_meta_ok','crate::r1_pool_adapter::owned::_::data_len'],
 opaque=['aspis_r1_cost_probe::verifier::tx1','crate::error'],modules=['AdapterRwModel'],basis='Changed shape after E004 (extended Not_found) and E005 (original: returns inside nested loops in require_distinct_accounts).')
add('D01b','prog','AdapterRw split b: require_distinct_accounts alone',['crate::r1_pool_adapter::owned::require_distinct_accounts'],modules=['AdapterRwModel'],basis='Changed shape after E004/E005.')
(E/'PCQD_extract_specs.json').write_text(json.dumps(dict(schema='PCQD_extract_specs/1',note='roots and opacity per group; extended Aeneas first. P1g.',specs=S),indent=1)+'\n')
print(len(S))
