//! Entry points to unchanged native helpers, for source-only extraction.
use aspis_core::{field::QM31, r0::{CodeField, domain::{FibreIndex, Point}}};
pub fn fibre<E:CodeField>(i:FibreIndex)->Point<E> { aspis_core::r0::domain::fibre_point(i) }
pub fn eval_message<E:CodeField>(q:&[E;1024], z:Point<E>)->E { aspis_core::r0::encoder::eval_message(q,z) }
pub fn boundary_sum(p:&[QM31;28])->QM31 { aspis_core::state_only_sumcheck::state_only_boundary_sum(p) }
pub fn eval_poly(p:&[QM31;28], x:QM31)->QM31 { aspis_core::state_only_sumcheck::evaluate_state_only_polynomial(p,x) }
pub fn multi(q:&[QM31], p:&[QM31;10])->Option<QM31> { aspis_statement::constraints_v4::multilinear_evaluate_qm31(q,p) }
pub fn copy_sum(q:&[QM31])->Option<QM31> { aspis_statement::state_only_semantic::state_only_copy_helper_sum(q) }
pub fn transition(p:aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>)->&aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1 { p.transition() }
pub fn late_eq(a:&aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1,b:&aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1)->bool { a==b }
