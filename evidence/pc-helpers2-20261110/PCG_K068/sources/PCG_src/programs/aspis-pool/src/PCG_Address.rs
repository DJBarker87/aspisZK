extern crate alloc;
use solana_program::pubkey::{Pubkey,PubkeyError};
use core::cell::Cell;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[path="PCG_address_reference.rs"] pub(crate) mod reference;
#[repr(C)]
pub(crate) struct Context<'a>{pub(crate) program:Pubkey,pub(crate) request:reference::Request,pub(crate) outer:*const &'a[u8],pub(crate) reply:Pubkey,pub(crate) bump:u8,pub(crate) is_ok:bool,pub(crate) error:u8,pub(crate) calls:Cell<u8>}
fn create_reply(seeds:&[&[u8]],program:&Pubkey)->Result<Pubkey,PubkeyError>{
 let c=unsafe{&*(program as *const Pubkey as *const Context<'_>)};
 assert_eq!(seeds.as_ptr(),c.outer);assert_eq!(seeds.len(),c.request.count);c.calls.set(c.calls.get()+1);
 if c.is_ok{Ok(c.reply)}else{Err(match c.error{0=>PubkeyError::MaxSeedLengthExceeded,1=>PubkeyError::InvalidSeeds,2=>PubkeyError::IllegalOwner,_=>unreachable!()})}
}
fn find_reply(seeds:&[&[u8]],program:&Pubkey)->(Pubkey,u8){
 let c=unsafe{&*(program as *const Pubkey as *const Context<'_>)};
 assert_eq!(seeds.len(),c.request.count);
 for i in 0..c.request.count{assert_eq!(seeds[i],&c.request.seeds[i][..c.request.lengths[i]]);}
 c.calls.set(c.calls.get()+1);(c.reply,c.bump)
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Pubkey::create_program_address,create_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stored_matches(){
 let storage:[u8;32]=kani::any();let len:usize=kani::any();kani::assume(len<=32);let n:usize=kani::any();kani::assume(n<=16);
 let parts:[&[u8];16]=[&storage[..len];16];let key=Pubkey::new_from_array(kani::any());let error:u8=kani::any();kani::assume(error<3);
 let program:[u8;32]=kani::any();let c=Context{program:Pubkey::new_from_array(program),request:reference::Request{program,seeds:[[0;32];4],lengths:[0;4],count:n},outer:parts.as_ptr(),reply:Pubkey::new_from_array(kani::any()),bump:kani::any(),is_ok:kani::any(),error,calls:Cell::new(0)};
 let got=crate::registry::stored_bump_address_matches(&parts[..n],&c.program,&key);
 assert_eq!(c.calls.get(),1);let expected=c.is_ok&&c.reply==key;
 assert!((got==expected)!=cfg!(PCG_NEG_ADDRESS));
}
// Generated exact-request helper harnesses.
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Pubkey::find_program_address,find_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn request_374(){let program:[u8;32]=kani::any();let pool:[u8;32]=kani::any();let profile:[u8;32]=kani::any();let release:[u8;32]=kani::any();let request=reference::request_374(program,pool,profile,release);let c=Context{program:Pubkey::new_from_array(program),request,outer:core::ptr::null(),reply:Pubkey::new_from_array(kani::any()),bump:kani::any(),is_ok:true,error:0,calls:Cell::new(0)};let got=crate::registry::pool_v1_verifier_entry_address(&c.program,&Pubkey::new_from_array(pool),&profile,&release);assert_eq!(c.calls.get(),1);assert!((got==(c.reply,c.bump))!=cfg!(PCG_NEG_ADDRESS));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Pubkey::find_program_address,find_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn request_375(){let program:[u8;32]=kani::any();let pool:[u8;32]=kani::any();let profile:[u8;32]=kani::any();let release:[u8;32]=kani::any();let request=reference::request_375(program,pool,profile,release);let c=Context{program:Pubkey::new_from_array(program),request,outer:core::ptr::null(),reply:Pubkey::new_from_array(kani::any()),bump:kani::any(),is_ok:true,error:0,calls:Cell::new(0)};let got=crate::registry::pool_v1_verifier_entry_v2_address(&c.program,&Pubkey::new_from_array(pool),&profile,&release);assert_eq!(c.calls.get(),1);assert!((got==(c.reply,c.bump))!=cfg!(PCG_NEG_ADDRESS));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Pubkey::find_program_address,find_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn request_376(){let program:[u8;32]=kani::any();let pool:[u8;32]=kani::any();let request=reference::request_376(program,pool);let c=Context{program:Pubkey::new_from_array(program),request,outer:core::ptr::null(),reply:Pubkey::new_from_array(kani::any()),bump:kani::any(),is_ok:true,error:0,calls:Cell::new(0)};let got=crate::registry::pool_v1_verifier_registry_address(&c.program,&Pubkey::new_from_array(pool));assert_eq!(c.calls.get(),1);assert!((got==(c.reply,c.bump))!=cfg!(PCG_NEG_ADDRESS));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Pubkey::find_program_address,find_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn request_377(){let program:[u8;32]=kani::any();let pool:[u8;32]=kani::any();let request=reference::request_377(program,pool);let c=Context{program:Pubkey::new_from_array(program),request,outer:core::ptr::null(),reply:Pubkey::new_from_array(kani::any()),bump:kani::any(),is_ok:true,error:0,calls:Cell::new(0)};let got=crate::registry::pool_v1_verifier_registry_v2_address(&c.program,&Pubkey::new_from_array(pool));assert_eq!(c.calls.get(),1);assert!((got==(c.reply,c.bump))!=cfg!(PCG_NEG_ADDRESS));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Pubkey::find_program_address,find_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn request_390(){let program:[u8;32]=kani::any();let pool:[u8;32]=kani::any();let request=reference::request_390(program,pool);let c=Context{program:Pubkey::new_from_array(program),request,outer:core::ptr::null(),reply:Pubkey::new_from_array(kani::any()),bump:kani::any(),is_ok:true,error:0,calls:Cell::new(0)};let got=crate::vault::pool_v1_vault_authority_address(&c.program,&Pubkey::new_from_array(pool));assert_eq!(c.calls.get(),1);assert!((got==(c.reply,c.bump))!=cfg!(PCG_NEG_ADDRESS));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Pubkey::find_program_address,find_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn request_391(){let program:[u8;32]=kani::any();let pool:[u8;32]=kani::any();let request=reference::request_391(program,pool);let c=Context{program:Pubkey::new_from_array(program),request,outer:core::ptr::null(),reply:Pubkey::new_from_array(kani::any()),bump:kani::any(),is_ok:true,error:0,calls:Cell::new(0)};let got=crate::vault::pool_v1_vault_token_account_address(&c.program,&Pubkey::new_from_array(pool));assert_eq!(c.calls.get(),1);assert!((got==(c.reply,c.bump))!=cfg!(PCG_NEG_ADDRESS));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Pubkey::find_program_address,find_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn request_323(){let program:[u8;32]=kani::any();let pool:[u8;32]=kani::any();let sequence:u64=kani::any();let request=reference::request_323(program,pool,sequence);let c=Context{program:Pubkey::new_from_array(program),request,outer:core::ptr::null(),reply:Pubkey::new_from_array(kani::any()),bump:kani::any(),is_ok:true,error:0,calls:Cell::new(0)};let got=crate::pair_forest::pool_v1_pair_forest_checkpoint_address(&c.program,&Pubkey::new_from_array(pool),sequence);assert_eq!(c.calls.get(),1);assert!((got==(c.reply,c.bump))!=cfg!(PCG_NEG_ADDRESS));}
