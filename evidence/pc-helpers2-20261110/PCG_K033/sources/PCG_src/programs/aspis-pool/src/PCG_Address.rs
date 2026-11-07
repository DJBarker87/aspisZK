extern crate alloc;
use solana_program::pubkey::{Pubkey,PubkeyError};
use core::cell::Cell;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[path="PCG_address_reference.rs"] mod reference;
#[repr(C)]
struct Context<'a>{program:Pubkey,request:reference::Request,outer:*const &'a[u8],reply:Pubkey,bump:u8,is_ok:bool,error:u8,calls:Cell<u8>}
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
