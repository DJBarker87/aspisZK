"""Extract one unchanged helper and its explicitly listed native dependencies."""
from pathlib import Path
import subprocess,os,sys
r=Path(__file__).resolve().parents[3];d=Path(__file__).with_name('direct');owner=sys.argv[1]
roots={
 'transition':['aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::_::transition','aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::_::semantic','aspis_statement::pool_v1::pair_forest_semantic_terminal::private_public','aspis_statement::pool_v1::pair_forest_semantic_terminal::withdrawal_public'],
 'late_eq':['aspis_statement::pool_v1::pair_tree_profile::_::eq','aspis_statement::pool_v1::pair_terminal::_::eq'],
 'fibre':['aspis_core::r0::domain::fibre_point','aspis_core::r0::domain::rev18'],
 'eval_message':['aspis_core::r0::encoder','aspis_core::r0::basis'],
 'boundary_sum':['aspis_core::state_only_sumcheck::state_only_boundary_sum'],
 'eval_poly':['aspis_core::state_only_sumcheck::evaluate_state_only_polynomial','aspis_core::state_only_sumcheck::evaluate_state_only_polynomial_horner'],
 'multi':['aspis_statement::constraints_v4::multilinear_evaluate_qm31'],
 'copy_sum':['aspis_statement::state_only_semantic::state_only_copy_helper_sum']}
assert owner in roots
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','aspis_core','--opaque','aspis_statement','--start-from','crate::'+owner]
for x in roots[owner]+['aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::r0::domain::FibreIndex','aspis_core::r0::domain::Point','aspis_core::r0::scalar::CodeField','aspis_statement::pool_v1::pair_forest_semantic_terminal::CompiledVariant','aspis_statement::pool_v1::pair_forest_semantic_terminal::SemanticPublic','aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public','aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1','aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1','aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1','aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1','aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1']:
 cmd+=['--include',x]
cmd+=['--dest-file',str(r/('ProverRwDirect'+owner+'.llbc')),'--','--manifest-path',str(d/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
