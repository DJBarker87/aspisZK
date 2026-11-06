use super::*;
pub(super) fn reference(s:AuthenticatedVerifierSelectionV1,pool:[u8;32],verifier_program:[u8;32],profile_binding:[u8;32],release_binding:[u8;32],statement_version:u8)->bool {
 s.pool==pool && s.verifier_program==verifier_program && s.profile_binding==profile_binding && s.release_binding==release_binding && s.statement_version==statement_version
}
#[cfg(kani)] #[kani::proof_for_contract(AuthenticatedVerifierSelectionV1::matches)]
fn matches_contract(){let s:AuthenticatedVerifierSelectionV1=kani::any();let _=s.matches(kani::any(),kani::any(),kani::any(),kani::any(),kani::any());}
