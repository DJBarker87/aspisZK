use super::*;
pub(super) fn reference(s:AuthenticatedVerifierSelectionV1,owner:&Pubkey)->bool {
 match s.expected_verifier_loader {None=>true,Some(expected)=>owner.to_bytes()==expected}
}
#[cfg(kani)] #[kani::proof_for_contract(AuthenticatedVerifierSelectionV1::matches_verifier_owner)]
fn owner_contract(){let s:AuthenticatedVerifierSelectionV1=kani::any();let owner=Pubkey::new_from_array(kani::any());let _=s.matches_verifier_owner(&owner);}
