"""Extract one native callback with the existing unmodified pinned tools."""
from pathlib import Path
import os,subprocess,sys
r=Path(__file__).resolve().parents[3]
owner=sys.argv[1]
assert owner in ['late_eq','eval_poly','copy_sum','trace_clone','fibre','reverse32']
p=r/('tools/prover-rw-20261023/success-p7/proof/Cargo.toml' if owner in ['trace_clone','reverse32'] else 'tools/prover-rw-20261023/success-p6/direct/Cargo.toml')
roots={
 'reverse32':[],
 'fibre':['aspis_core::r0::domain::fibre_point','aspis_core::r0::domain::rev18','aspis_core::field::_::pow','aspis_core::field::_::ONE','aspis_core::field::_::new','aspis_core::field::_::square'],
 'trace_clone':['aspis_statement::state_only_trace::StateOnlyTraceFoundation','aspis_statement::state_only_trace::_::clone'],
 'late_eq':['aspis_statement::pool_v1::pair_tree_profile::_::eq','aspis_statement::pool_v1::pair_terminal::_::eq'],
 'eval_poly':['aspis_core::state_only_sumcheck::evaluate_state_only_polynomial','aspis_core::state_only_sumcheck::evaluate_state_only_polynomial::closure','aspis_core::field::PreparedQm31Multiplier','aspis_core::field::_::new','aspis_core::field::_::mul','aspis_core::field::_::square','aspis_core::field::qm31_sum_products3','aspis_core::field::qm31_sum_products_small','aspis_core::field::qm31_from_karatsuba_channel_sums','aspis_core::field::mul_by_r'],
 'copy_sum':['aspis_statement::state_only_semantic::state_only_copy_helper_sum']}
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','aspis_core','--opaque','aspis_statement','--start-from','crate::'+owner]
for x in roots[owner]+['aspis_core::r0::domain::FibreIndex','aspis_core::r0::domain::Point','aspis_core::r0::scalar::CodeField','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1','aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1','aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1']:
 cmd+=['--include',x]
cmd+=['--dest-file',str(r/('ProverRwP7'+owner+'.llbc')),'--','--manifest-path',str(p),'--release','--offline','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
