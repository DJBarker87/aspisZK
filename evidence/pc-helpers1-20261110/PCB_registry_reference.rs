#[derive(Clone,Copy)]
pub struct VerifierPolicyV1 {pub flags:u8,pub registry_program:[u8;32],pub registry_authority:[u8;32],pub policy_binding:[u8;32]}
#[derive(Clone,Copy)]
pub struct AuthenticatedVerifierSelectionV1 {pub policy:VerifierPolicyV1,pub pool:[u8;32],pub verifier_program:[u8;32],pub profile_binding:[u8;32],pub release_binding:[u8;32],pub statement_version:u8,pub registry_generation:u64,pub expected_verifier_loader:Option<[u8;32]>,pub authenticated_at_slot:u64}
#[derive(Clone,Copy)] pub struct Pubkey(pub [u8;32]);
impl Pubkey {pub fn to_bytes(self)->[u8;32] {self.0}}
pub fn matches_ref(s:AuthenticatedVerifierSelectionV1,pool:[u8;32],verifier_program:[u8;32],profile_binding:[u8;32],release_binding:[u8;32],statement_version:u8)->bool {
 s.pool==pool && s.verifier_program==verifier_program && s.profile_binding==profile_binding && s.release_binding==release_binding && s.statement_version==statement_version
}
pub fn owner_ref(s:AuthenticatedVerifierSelectionV1,owner:&Pubkey)->bool {
 match s.expected_verifier_loader {None=>true,Some(expected)=>owner.to_bytes()==expected}
}
