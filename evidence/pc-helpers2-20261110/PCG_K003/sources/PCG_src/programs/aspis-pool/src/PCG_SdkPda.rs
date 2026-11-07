extern crate alloc;
use solana_program::pubkey::{Pubkey,PubkeyError};
use core::cell::Cell;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// The first member is the only member visible to the actual SDK wrapper.
// The syscall oracle recovers this harness-owned local context by provenance.
#[repr(C)]
struct Context<'a>{program:Pubkey,seeds:*const &'a[u8],count:usize,reply:[u8;32],bump:u8,status:u64,calls:Cell<u8>}
unsafe fn create_oracle(seeds:*const u8,n:u64,program:*const u8,out:*const u8)->u64{
 let c=&*(program as *const Context<'_>);
 assert_eq!(seeds,c.seeds as *const u8);assert_eq!(n,c.count as u64);
 c.calls.set(c.calls.get()+1);
 *(out as *mut [u8;32])=c.reply;
 c.status
}
unsafe fn find_oracle(seeds:*const u8,n:u64,program:*const u8,out:*const u8,bump:*const u8)->u64{
 let c=&*(program as *const Context<'_>);
 assert_eq!(seeds,c.seeds as *const u8);assert_eq!(n,c.count as u64);
 c.calls.set(c.calls.get()+1);
 *(out as *mut [u8;32])=c.reply;*(bump as *mut u8)=c.bump;
 c.status
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(solana_program::pubkey::syscalls::sol_create_program_address,create_oracle)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn create_forward(){
 let storage:[[u8;32];16]=kani::any();let lengths:[usize;16]=kani::any();
 let mut parts:[&[u8];16]=[&[];16];for i in 0..16{kani::assume(lengths[i]<=32);parts[i]=&storage[i][..lengths[i]];}
 let n:usize=kani::any();kani::assume(n<=1);let status:u64=kani::any();kani::assume(status<=2);
 let c=Context{program:Pubkey::new_from_array(kani::any()),seeds:parts.as_ptr(),count:n,reply:kani::any(),bump:kani::any(),status,calls:Cell::new(0)};
 let got=Pubkey::create_program_address(&parts[..n],&c.program);
 assert_eq!(c.calls.get(),1);
 let want=match status{0=>Ok(Pubkey::new_from_array(c.reply)),1=>Err(PubkeyError::InvalidSeeds),2=>Err(PubkeyError::IllegalOwner),_=>unreachable!()};
 assert!((got==want)!=cfg!(PCG_NEG_PDA));
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(solana_program::pubkey::syscalls::sol_try_find_program_address,find_oracle)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn find_forward(){
 let storage:[[u8;32];16]=kani::any();let lengths:[usize;16]=kani::any();
 let mut parts:[&[u8];16]=[&[];16];for i in 0..16{kani::assume(lengths[i]<=32);parts[i]=&storage[i][..lengths[i]];}
 let n:usize=kani::any();kani::assume(n<=16);let status:u64=kani::any();
 let c=Context{program:Pubkey::new_from_array(kani::any()),seeds:parts.as_ptr(),count:n,reply:kani::any(),bump:kani::any(),status,calls:Cell::new(0)};
 let got=Pubkey::try_find_program_address(&parts[..n],&c.program);
 assert_eq!(c.calls.get(),1);
 let want=if status==0{Some((Pubkey::new_from_array(c.reply),c.bump))}else{None};
 assert!((got==want)!=cfg!(PCG_NEG_PDA));
}
