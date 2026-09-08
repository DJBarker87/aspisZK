// Exact pinned production source modules, compiled only by the research harness.
fn multilinear_eval(v:&[aspis_core::field::M31],p:&[aspis_core::field::QM31])->aspis_core::field::QM31{
    aspis_statement::multilinear_evaluate_qm31(&v.iter().map(|x|aspis_core::field::QM31::from_cm31(aspis_core::field::CM31::from_m31(*x))).collect::<Vec<_>>(),p.try_into().unwrap()).unwrap()
}
fn multilinear_eval_extension(v:&[aspis_core::field::QM31],p:&[aspis_core::field::QM31])->aspis_core::field::QM31{
    aspis_statement::multilinear_evaluate_qm31(v,p.try_into().unwrap()).unwrap()
}
#[path="../../../../crates/aspis-prover/src/circle_candidate.rs"]
pub mod circle_candidate;
#[path="../../../../crates/aspis-prover/src/circle_candidate_openings.rs"]
pub mod circle_candidate_openings;
#[path="../../../../crates/aspis-prover/src/state_only_hiding.rs"]
pub mod state_only_hiding;
#[path="../../../../crates/aspis-prover/src/state_only_zerocheck.rs"]
pub mod state_only_zerocheck;
#[path="../../../../crates/aspis-prover/src/state_only_entropy.rs"]
pub mod state_only_entropy;
