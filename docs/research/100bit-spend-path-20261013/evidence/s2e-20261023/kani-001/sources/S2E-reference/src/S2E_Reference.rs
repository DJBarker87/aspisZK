#![cfg(any(kani, aeneas_ref))]
#![allow(dead_code, unexpected_cfgs)]
use aspis_r1_cost_probe::{verifier, transport::Variant};
use aspis_statement::pool_v1::{PoolV1PairForestTerminalStatementV1 as Statement,
 PoolV1PairVerifiedAfterstateV1 as Afterstate,
 POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
 POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC,
 POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES};
use solana_program::{program_error::ProgramError, entrypoint::ProgramResult};

// Abstract child interface. Every call returns its actual state effects, even Err.
// No implementation or successful-child axiom is supplied here. Concrete contracts
// must bind these operations to the installed children, including allocation/abort.
pub trait Children {
 type State;
 fn decode(state: &mut Self::State, bytes: &[u8]) -> Result<Box<Statement>,ProgramError>;
 fn validate(state: &mut Self::State, statement: &Statement) -> ProgramResult;
 fn candidate(state: &mut Self::State, afterstate: &Afterstate) -> Result<[u8;688],ProgramError>;
 fn first(state: &mut Self::State, statement: &Statement, public: &[u8], proof: &[u8], split: usize)
     -> Result<Vec<u8>,ProgramError>;
 fn copy(state: &mut Self::State, sdk: &mut OwnedSdk, slot: usize, checkpoint: &[u8]);
 fn drop_checkpoint(state: &mut Self::State, checkpoint: Vec<u8>);
 fn drop_statement(state: &mut Self::State, statement: Box<Statement>);
 fn validate_asq8(state: &mut Self::State, program: [u8;32], sdk: &OwnedSdk, data: &[u8])
     -> Result<Validated,ProgramError>;
 fn public(state: &mut Self::State, statement: &Statement) -> Result<Vec<u8>,ProgramError>;
 fn second(state: &mut Self::State, public: &[u8], proof: &[u8], checkpoint: &[u8]) -> ProgramResult;
 fn emit(state: &mut Self::State, statement: &Statement) -> ProgramResult;
 fn clear_return_data(state: &mut Self::State);
}
pub struct Validated { pub statement: Box<Statement>, pub proof_length: usize }
#[derive(Clone,Copy)]
pub struct OwnedAccount {
 pub key:[u8;32],pub owner:[u8;32],pub is_signer:bool,pub is_writable:bool,
 pub executable:bool,pub rent_epoch:u64,pub data_slot:usize,pub lamports_slot:usize,
}
pub struct OwnedDataCell {
 pub bytes:Vec<u8>,pub borrowed:isize,pub strong:usize,pub weak:usize,
}
pub struct OwnedLamportsCell {
 pub amount:u64,pub borrowed:isize,pub strong:usize,pub weak:usize,
}
pub struct OwnedSdk {
 pub accounts:Vec<OwnedAccount>,pub data_cells:Vec<OwnedDataCell>,
 pub lamports_cells:Vec<OwnedLamportsCell>,
}
pub struct LiveGuards {
 pub checkpoint:Option<usize>,pub public:Option<usize>,pub proof:Option<usize>,
}

pub fn shared_allowed(counter:isize)->bool {counter>=0 && counter<isize::MAX}
// The real SDK length helper acquires/drops a temporary shared guard.
pub fn owned_data_len(sdk:&OwnedSdk,slot:usize)->Result<usize,ProgramError> {
 if shared_allowed(sdk.data_cells[slot].borrowed) {Ok(sdk.data_cells[slot].bytes.len())}
 else {Err(ProgramError::AccountBorrowFailed)}
}
pub fn owned_acquire_checkpoint(sdk:&mut OwnedSdk,guards:&mut LiveGuards,slot:usize)->ProgramResult {
 if sdk.data_cells[slot].borrowed!=0 {return Err(ProgramError::AccountBorrowFailed);}
 sdk.data_cells[slot].borrowed=-1;
 guards.checkpoint=Some(slot);
 Ok(())
}
pub fn owned_acquire_shared(sdk:&mut OwnedSdk,slot:usize)->ProgramResult {
 let count=sdk.data_cells[slot].borrowed;
 if !shared_allowed(count) {return Err(ProgramError::AccountBorrowFailed);}
 sdk.data_cells[slot].borrowed=count.checked_add(1).unwrap();
 Ok(())
}
pub fn owned_release_guards(sdk:&mut OwnedSdk,guards:LiveGuards) {
 // Reverse acquisition order matches Rust local drop order, including aliases.
 if let Some(slot)=guards.proof {sdk.data_cells[slot].borrowed=sdk.data_cells[slot].borrowed.checked_sub(1).unwrap();}
 if let Some(slot)=guards.public {sdk.data_cells[slot].borrowed=sdk.data_cells[slot].borrowed.checked_sub(1).unwrap();}
 if let Some(slot)=guards.checkpoint {sdk.data_cells[slot].borrowed=sdk.data_cells[slot].borrowed.checked_add(1).unwrap();}
}

// Structural recursion avoids iterator/fixed-point extraction.
pub fn nonzero_from(bytes: &[u8], remaining: usize) -> bool {
 if remaining == 0 { false }
 else { bytes[bytes.len()-remaining] != 0 || nonzero_from(bytes,remaining-1) }
}
pub fn shape1(data: &[u8], accounts: usize) -> ProgramResult {
 if !(data == &[3,10] || data == &[3,11]) || accounts != 3 {
  Err(ProgramError::InvalidInstructionData)
 } else { Ok(()) }
}
pub fn admission(program: [u8;32], sdk: &OwnedSdk) -> ProgramResult {
 let proof=sdk.accounts[0]; let public=sdk.accounts[1]; let cp=sdk.accounts[2];
 if proof.key==public.key || proof.key==cp.key || public.key==cp.key {
  return Err(ProgramError::InvalidArgument);
 }
 if proof.is_signer || proof.is_writable || proof.executable {return Err(ProgramError::InvalidAccountData);}
 if public.is_signer || public.is_writable || public.executable {return Err(ProgramError::InvalidAccountData);}
 if cp.owner!=program || cp.is_signer || cp.executable || !cp.is_writable ||
     owned_data_len(sdk,cp.data_slot)? != verifier::checkpoint_size(Variant::S2) {
  return Err(ProgramError::InvalidAccountData);
 }
 Ok(())
}
pub fn proof_gate(proof: &[u8], candidate: &[u8;688]) -> ProgramResult {
 let start=POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
 let end=start.checked_add(verifier::PROOF_BYTES).ok_or(ProgramError::InvalidAccountData)?;
 if proof.len()!=end || proof[..start]!=*candidate || proof[start+8]!=Variant::S2.tag() {
  return Err(ProgramError::InvalidAccountData);
 }
 Ok(())
}
// The returned Vec is always dropped before the proof guard, even on a length error.
pub fn after_first<C: Children>(state: &mut C::State,sdk: &mut OwnedSdk,slot: usize,
 checkpoint: Vec<u8>) -> ProgramResult {
 let result=if checkpoint.len()!=sdk.data_cells[slot].bytes.len() {
  Err(ProgramError::InvalidAccountData)
 } else { C::copy(state,sdk,slot,&checkpoint); Ok(()) };
 C::drop_checkpoint(state,checkpoint);
 result
}
pub fn first_and_copy<C: Children>(state: &mut C::State,sdk: &mut OwnedSdk,
 statement: &Statement,public: &[u8],proof: &[u8],split: usize,cp_slot: usize) -> ProgramResult {
 let checkpoint=C::first(state,statement,public,&proof[688..58295],split)?;
 after_first::<C>(state,sdk,cp_slot,checkpoint)
}
pub fn proof_continuation<C: Children>(state: &mut C::State,sdk: &mut OwnedSdk,
 statement: &Statement,public: &[u8],data: &[u8],candidate: &[u8;688]) -> ProgramResult {
 let proof_slot=sdk.accounts[0].data_slot; let cp_slot=sdk.accounts[2].data_slot;
 owned_acquire_shared(sdk,proof_slot)?;
 let proof=sdk.data_cells[proof_slot].bytes.clone();
 let result=match proof_gate(&proof,candidate) {
  Ok(()) => first_and_copy::<C>(state,sdk,statement,public,&proof,data[1] as usize,cp_slot),
  Err(e) => Err(e),
 };
 sdk.data_cells[proof_slot].borrowed=sdk.data_cells[proof_slot].borrowed.checked_sub(1).unwrap();
 result
}
pub fn statement_continuation<C: Children>(state: &mut C::State,sdk: &mut OwnedSdk,
 statement: &Statement,public: &[u8],data: &[u8]) -> ProgramResult {
 C::validate(state,statement).map_err(|_|ProgramError::InvalidAccountData)?;
 let candidate=C::candidate(state,&statement.common().lane_transition.candidate_afterstate)
     .map_err(|_|ProgramError::InvalidAccountData)?;
 proof_continuation::<C>(state,sdk,statement,public,data,&candidate)
}
pub fn decoded_continuation<C: Children>(state: &mut C::State,sdk: &mut OwnedSdk,
 public: &[u8],data: &[u8]) -> ProgramResult {
 let statement=C::decode(state,public)?;
 let result=statement_continuation::<C>(state,sdk,&statement,public,data);
 C::drop_statement(state,statement);
 result
}
pub fn public_continuation<C: Children>(state: &mut C::State,sdk: &mut OwnedSdk,data: &[u8]) -> ProgramResult {
 let slot=sdk.accounts[1].data_slot;
 owned_acquire_shared(sdk,slot)?;
 let public=sdk.data_cells[slot].bytes.clone();
 let result=decoded_continuation::<C>(state,sdk,&public,data);
 sdk.data_cells[slot].borrowed=sdk.data_cells[slot].borrowed.checked_sub(1).unwrap();
 result
}
pub fn checkpoint_continuation<C: Children>(state: &mut C::State,sdk: &mut OwnedSdk,data: &[u8]) -> ProgramResult {
 let slot=sdk.accounts[2].data_slot;
 if nonzero_from(&sdk.data_cells[slot].bytes,sdk.data_cells[slot].bytes.len()) {
  return Err(ProgramError::AccountAlreadyInitialized);
 }
 public_continuation::<C>(state,sdk,data)
}
pub fn stage1<C: Children>(state: &mut C::State,sdk: &mut OwnedSdk,program: [u8;32],data: &[u8]) -> ProgramResult {
 shape1(data,sdk.accounts.len())?;
 admission(program,sdk)?;
 let slot=sdk.accounts[2].data_slot;
 let mut guards=LiveGuards{checkpoint:None,public:None,proof:None};
 owned_acquire_checkpoint(sdk,&mut guards,slot)?;
 let result=checkpoint_continuation::<C>(state,sdk,data);
 owned_release_guards(sdk,guards);
 result
}
pub fn stage2_tail<C: Children>(state: &mut C::State,sdk: &OwnedSdk,
 validated: &Validated,proof_slot: usize,cp_slot: usize) -> ProgramResult {
 let proof=&sdk.data_cells[proof_slot].bytes;
 let end=688usize.checked_add(validated.proof_length).ok_or(ProgramError::InvalidAccountData)?;
 if proof.len()!=end {return Err(ProgramError::InvalidAccountData);}
 let public=C::public(state,&validated.statement).map_err(|_|ProgramError::InvalidInstructionData)?;
 if public.len()!=POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES {return Err(ProgramError::InvalidInstructionData);}
 C::second(state,&public,&proof[688..end],&sdk.data_cells[cp_slot].bytes)?;
 C::emit(state,&validated.statement)
}
pub fn stage2_checkpoint<C: Children>(state: &mut C::State,sdk: &mut OwnedSdk,
 validated: &Validated,proof_slot: usize) -> ProgramResult {
 let slot=sdk.accounts[6].data_slot;
 owned_acquire_shared(sdk,slot)?;
 let result=stage2_tail::<C>(state,sdk,validated,proof_slot,slot);
 sdk.data_cells[slot].borrowed=sdk.data_cells[slot].borrowed.checked_sub(1).unwrap();
 result
}
pub fn stage2_proof<C: Children>(state: &mut C::State,sdk: &mut OwnedSdk,validated: &Validated) -> ProgramResult {
 let slot=sdk.accounts[0].data_slot;
 owned_acquire_shared(sdk,slot)?;
 let result=stage2_checkpoint::<C>(state,sdk,validated,slot);
 sdk.data_cells[slot].borrowed=sdk.data_cells[slot].borrowed.checked_sub(1).unwrap();
 result
}
pub fn stage2<C: Children>(state: &mut C::State,sdk: &mut OwnedSdk,program: [u8;32],data: &[u8]) -> ProgramResult {
 if sdk.accounts.len()!=7 || data.get(..4)!=Some(&POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[..]) {
  return Err(ProgramError::InvalidInstructionData);
 }
 C::clear_return_data(state);
 let validated=C::validate_asq8(state,program,sdk,data)?;
 let result=stage2_proof::<C>(state,sdk,&validated);
 C::drop_statement(state,validated.statement);
 result
}
