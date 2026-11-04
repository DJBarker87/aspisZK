use super::*;
struct NFC_DotInputLog { proof:usize,coefficients:usize,called:bool }
fn NFC_dots_input(log:&mut NFC_DotInputLog,q:&[u8],g:&[E;29]) {
 // Literal first operation of fast_dots::four_dots, before its four children.
 let prefix:&[u8;608]=q[..608].try_into().unwrap();
 log.proof=prefix.as_ptr() as usize;log.coefficients=g.as_ptr() as usize;log.called=true;
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFC_copy::KMX_copy_nonoverlapping)]
fn query_dots_window() {
 let proof=kani::vec::exact_vec::<u8,{compact::PROOF_BYTES}>();
 let i:usize=kani::any();kani::assume(i<22);
 let g:[E;29]=kani::any();let q=opening(&proof,i);
 let at:usize=kani::any();kani::assume(at<608);
 let start=compact::OFF_OPENINGS+i*OPENING;
 assert_eq!(q.len(),OPENING);assert_eq!(q.as_ptr() as usize,proof.as_ptr() as usize+start);
 let mut log=NFC_DotInputLog{proof:0,coefficients:0,called:false};NFC_dots_input(&mut log,q,&g);
 assert!(log.called);assert_eq!(log.coefficients,g.as_ptr() as usize);
 assert_eq!(q[at],proof[start+at]);
 let expected=proof.as_ptr() as usize+start;
 assert_eq!(log.proof,if cfg!(NFC_wrong_query_window){expected+1}else{expected});
}
// Split of K021: an arbitrary opening window, not a whole proof allocation.
// Its association with the outer proof remains a separate parent obligation.
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFC_copy::KMX_copy_nonoverlapping)]
fn opening_prefix_window() {
 let source:[u8;OPENING]=kani::any();let g:[E;29]=kani::any();
 let at:usize=kani::any();kani::assume(at<608);
 let mut log=NFC_DotInputLog{proof:0,coefficients:0,called:false};
 NFC_dots_input(&mut log,&source,&g);
 assert!(log.called);assert_eq!(log.coefficients,g.as_ptr() as usize);
 assert_eq!(log.proof,source.as_ptr() as usize);
 let prefix:&[u8;608]=source[..608].try_into().unwrap();
 let expected=source[at];
 assert_eq!(prefix[at],if cfg!(NFC_wrong_opening_prefix){expected^1}else{expected});
}
