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

// Source-ordered SDK segment: the deployed syscall tail after seed validation.
// PCG_sdk_source.py checks this block against pinned SDK lib.rs943..959;
// only the crate-path spelling and SUCCESS constant are resolved locally.
fn create_tail(seeds:&[&[u8]],program_id:&Pubkey)->Result<Pubkey,PubkeyError>{
    let mut bytes = [0; 32];
    let result = unsafe {
        solana_program::pubkey::syscalls::sol_create_program_address(
            seeds as *const _ as *const u8,
            seeds.len() as u64,
            program_id as *const _ as *const u8,
            &mut bytes as *mut _ as *mut u8,
        )
    };
    match result {
        0 => Ok(Pubkey::from(bytes)),
        _ => Err(result.into()),
    }
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(solana_program::pubkey::syscalls::sol_create_program_address,create_oracle)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn create_tail_forward(){
 let storage:[u8;32]=kani::any();let parts:[&[u8];16]=[&storage;16];
 let n:usize=kani::any();kani::assume(n<=16);let status:u64=kani::any();kani::assume(status<=2);
 let c=Context{program:Pubkey::new_from_array(kani::any()),seeds:parts.as_ptr(),count:n,reply:kani::any(),bump:kani::any(),status,calls:Cell::new(0)};
 let got=create_tail(&parts[..n],&c.program);
 assert_eq!(c.calls.get(),1);
 let want=match status{0=>Ok(Pubkey::new_from_array(c.reply)),1=>Err(PubkeyError::InvalidSeeds),2=>Err(PubkeyError::IllegalOwner),_=>unreachable!()};
 assert!((got==want)!=cfg!(PCG_NEG_PDA));
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(solana_program::pubkey::syscalls::sol_create_program_address,create_oracle)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn create_validation_step(){
 let storage:[u8;33]=kani::any();let len:usize=kani::any();kani::assume(len<=33);let parts=[&storage[..len]];
 let status:u64=kani::any();kani::assume(status<=2);
 let c=Context{program:Pubkey::new_from_array(kani::any()),seeds:parts.as_ptr(),count:1,reply:kani::any(),bump:kani::any(),status,calls:Cell::new(0)};
 let got=Pubkey::create_program_address(&parts,&c.program);
 let want=if len>32{Err(PubkeyError::MaxSeedLengthExceeded)}else{match status{0=>Ok(Pubkey::new_from_array(c.reply)),1=>Err(PubkeyError::InvalidSeeds),2=>Err(PubkeyError::IllegalOwner),_=>unreachable!()}};
 assert_eq!(c.calls.get(),if len>32{0}else{1});
 assert!((got==want)!=cfg!(PCG_NEG_PDA));
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(solana_program::pubkey::syscalls::sol_try_find_program_address,find_oracle)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn find_success(){
 let storage:[u8;32]=kani::any();let parts:[&[u8];16]=[&storage;16];let n:usize=kani::any();kani::assume(n<=16);
 let c=Context{program:Pubkey::new_from_array(kani::any()),seeds:parts.as_ptr(),count:n,reply:kani::any(),bump:kani::any(),status:0,calls:Cell::new(0)};
 let got=Pubkey::find_program_address(&parts[..n],&c.program);assert_eq!(c.calls.get(),1);
 assert!((got==(Pubkey::new_from_array(c.reply),c.bump))!=cfg!(PCG_NEG_PDA));
}
#[kani::proof] #[kani::should_panic] #[kani::unwind(70)]
#[kani::stub(solana_program::pubkey::syscalls::sol_try_find_program_address,find_oracle)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn find_rejection(){
 let parts:[&[u8];0]=[];let status:u64=kani::any();kani::assume(status!=0);
 let c=Context{program:Pubkey::new_from_array(kani::any()),seeds:parts.as_ptr(),count:0,reply:kani::any(),bump:kani::any(),status,calls:Cell::new(0)};
 if !cfg!(PCG_NEG_PDA){let _=Pubkey::find_program_address(&parts,&c.program);}
}
#[kani::proof] #[kani::should_panic] #[kani::unwind(70)]
#[kani::stub(solana_program::pubkey::syscalls::sol_create_program_address,create_oracle)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn create_unknown_status(){
 let parts:[&[u8];0]=[];let status:u64=kani::any();kani::assume(status>2);
 let c=Context{program:Pubkey::new_from_array(kani::any()),seeds:parts.as_ptr(),count:0,reply:kani::any(),bump:kani::any(),status,calls:Cell::new(0)};
 if !cfg!(PCG_NEG_PDA){let _=Pubkey::create_program_address(&parts,&c.program);}
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(solana_program::pubkey::syscalls::sol_create_program_address,create_oracle)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn create_count_rejection(){
 let parts:[&[u8];17]=[&[];17];
 let c=Context{program:Pubkey::new_from_array(kani::any()),seeds:parts.as_ptr(),count:17,reply:kani::any(),bump:kani::any(),status:kani::any(),calls:Cell::new(0)};
 let got=Pubkey::create_program_address(&parts,&c.program);assert_eq!(c.calls.get(),0);
 assert!((got==Err(PubkeyError::MaxSeedLengthExceeded))!=cfg!(PCG_NEG_PDA));
}
