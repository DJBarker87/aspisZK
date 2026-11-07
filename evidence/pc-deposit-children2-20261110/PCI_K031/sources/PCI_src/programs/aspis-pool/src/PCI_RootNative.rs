extern crate alloc;
use super::*;
use core::cell::Cell;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[repr(C)]
struct Context{program:Pubkey,pool:[u8;32],page:u64,reply:Pubkey,bump:u8,calls:Cell<u8>}
fn find_reply(seeds:&[&[u8]],program:&Pubkey)->(Pubkey,u8){
 let c=unsafe{&*(core::ptr::with_exposed_provenance::<Context>(program as *const Pubkey as usize))};
 assert_eq!(seeds.len(),3);
 assert_eq!(seeds[0],b"aspis-pool-root-page-v1");
 assert_eq!(seeds[1],&c.pool);
 assert_eq!(seeds[2],&c.page.to_le_bytes());
 c.calls.set(c.calls.get()+1);(c.reply,c.bump)
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Pubkey::find_program_address,find_reply)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn root_address(){
 let c=Context{program:Pubkey::new_from_array(kani::any()),pool:kani::any(),page:kani::any(),reply:Pubkey::new_from_array(kani::any()),bump:kani::any(),calls:Cell::new(0)};
 let _=core::ptr::addr_of!(c).expose_provenance();
 let mut pool=c.pool;
 #[cfg(PCI_ROOT_ARG_MUTANT)]{pool[0]^=1;}
 let got=pool_v1_root_page_address(&c.program,&Pubkey::new_from_array(pool),c.page);
 assert_eq!(c.calls.get(),1);
 assert!((got==(c.reply,c.bump))!=cfg!(PCI_NEG_ROOT));
}
