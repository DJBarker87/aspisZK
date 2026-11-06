use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
type F=PoolV1VerifierRegistryFormatError;
fn status(n:u8)->Result<VerifierEntryStatusV1,F>{match n{0=>Ok(VerifierEntryStatusV1::Pending),1=>Ok(VerifierEntryStatusV1::Active),2=>Ok(VerifierEntryStatusV1::Paused),3=>Ok(VerifierEntryStatusV1::Retired),_=>Err(F::InvalidStatus)}}
fn registry()->VerifierRegistryV1{VerifierRegistryV1{flags:kani::any(),bump:kani::any(),pool:kani::any(),authority:kani::any(),policy_binding:kani::any(),generation:kani::any(),minimum_activation_delay_slots:kani::any()}}
fn entry()->VerifierRegistryEntryV1{let tag:u8=kani::any();kani::assume(tag<4);VerifierRegistryEntryV1{status:status(tag).unwrap(),statement_version:kani::any(),bump:kani::any(),pool:kani::any(),verifier_program:kani::any(),profile_binding:kani::any(),release_binding:kani::any(),activation_slot:kani::any(),retirement_slot:kani::any(),policy_binding:kani::any()}}
pub(super) fn registry_ref(r:&VerifierRegistryV1)->Result<(),F>{if r.flags & !3 !=0{Err(F::UnsupportedFlags)}else if r.pool==[0;32]||r.policy_binding==[0;32]{Err(F::ZeroRequiredBinding)}else if (r.flags & 2 !=0)!=(r.authority==[0;32]){Err(F::InvalidAuthorityMode)}else if r.minimum_activation_delay_slots==0{Err(F::InvalidActivationDelay)}else{Ok(())}}
pub(super) fn entry_ref(e:&VerifierRegistryEntryV1)->Result<(),F>{if e.statement_version==0{Err(F::InvalidStatementVersion)}else if e.pool==[0;32]||e.verifier_program==[0;32]||e.profile_binding==[0;32]||e.release_binding==[0;32]||e.policy_binding==[0;32]{Err(F::ZeroRequiredBinding)}else if e.retirement_slot!=u64::MAX&&e.retirement_slot<=e.activation_slot{Err(F::InvalidRetirementSlot)}else{Ok(())}}

#[kani::proof_for_contract(super::validate_verifier_registry_v1)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_contract(){let r=registry();let _=super::validate_verifier_registry_v1(&r);}

#[kani::proof_for_contract(super::validate_verifier_registry_entry_v1)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn entry_contract(){let r=entry();let _=super::validate_verifier_registry_entry_v1(&r);}
