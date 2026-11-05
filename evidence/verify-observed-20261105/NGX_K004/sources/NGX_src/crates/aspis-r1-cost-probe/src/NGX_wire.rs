use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct Hash(u64);
impl aspis_core::Digest32 for Hash { fn digest(&self,_parts:&[&[u8]])->[u8;32] { panic!("state accessor must not hash") } }
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn state_value() {
 let state:[u8;32]=kani::any(); let hash:u64=kani::any(); let next:u8=kani::any();
 let t=SemanticTranscript{state,hash:Hash(hash),next_row:next};
 let out=t.state();let i:usize=kani::any();kani::assume(i<32);
 assert!((out[i]==state[i])!=cfg!(NGX_invert));
 assert_eq!(t.state[i],state[i]);assert_eq!(t.hash.0,hash);assert_eq!(t.next_row,next);
}
