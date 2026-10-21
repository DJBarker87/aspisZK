fn first_reference(public:aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize)->Result<Vec<u8>,ProgramError>{
verifier::tx1(public,public_bytes,proof,k,SolanaDigest,None).map_err(error)
}
fn second_reference(public:&[u8],proof:&[u8],checkpoint:&[u8],authenticated:bool)->Result<(),Error>{
parse_shape(proof)?;
if !authenticated {canonical_scan(proof)?;}
tx2_common(public,proof,checkpoint,SolanaDigest,None)
}
#[cfg(kani)] mod proofs {
use super::*;
unsafe fn reset(){EVENTS=[EMPTY;3];COUNT=0;}
#[kani::proof] #[kani::unwind(10)] fn first_dispatch_correspondence(){
let a:[u8;16]=kani::any();let b:[u8;32]=kani::any();let k:usize=kani::any();
let semantic:u32=kani::any();let fail:[bool;3]=kani::any();unsafe{FAIL=fail;reset();}
let public=aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public{value:semantic,bytes:&a};
let x=first_decoded(public,&a,&b,k);let xt=unsafe{EVENTS};let count=unsafe{COUNT};unsafe{reset();}
let y=first_reference(public,&a,&b,k);assert_eq!(x,y);assert_eq!(xt,unsafe{EVENTS});assert_eq!(count,unsafe{COUNT});assert_eq!(count,1);assert!(!xt[0].observer);
}
#[kani::proof] #[kani::unwind(10)] fn second_dispatch_correspondence(){
let a:[u8;16]=kani::any();let b:[u8;32]=kani::any();let c:[u8;8]=kani::any();
let authenticated:bool=kani::any();let fail:[bool;3]=kani::any();unsafe{FAIL=fail;reset();}
let x=if authenticated{tx2_authenticated(&a,&b,&c,SolanaDigest,observer())}else{tx2(&a,&b,&c,SolanaDigest,observer())};
let xt=unsafe{EVENTS};let count=unsafe{COUNT};unsafe{reset();}let y=second_reference(&a,&b,&c,authenticated);
assert_eq!(x,y);assert_eq!(xt,unsafe{EVENTS});assert_eq!(count,unsafe{COUNT});
}
}
