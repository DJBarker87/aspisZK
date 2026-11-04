use super::*;
use super::super::{EbyKDot,E,QM31};
// One opaque child call with a LOCAL owned reply record. No field arithmetic.
// The caller's pre-state is arbitrary; count=position is proved by NFC_TailState.
struct NFC_Reply { words:[u64;8],calls:usize,receiver:usize,count:usize }
fn NFC_push(reply:&mut NFC_Reply,receiver:&mut EbyKDot,_value:E,_scalar:QM31)->Result<(),()> {
 reply.receiver=receiver as *mut EbyKDot as usize;
 reply.count=receiver.count;reply.calls+=1;
 receiver.c0.sums=[reply.words[0],reply.words[1],reply.words[2],reply.words[3]];
 receiver.c1.sums=[reply.words[4],reply.words[5],reply.words[6],reply.words[7]];
 receiver.count+=1;Ok(())
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFC_copy::KMX_copy_nonoverlapping)]
fn tail_receiver_window() {
 let position:usize=kani::any();kani::assume(position<3);
 let left:[u64;4]=kani::any();let right:[u64;4]=kani::any();
 let mut receiver=EbyKDot{c0:Dot{sums:left},c1:Dot{sums:right},count:position};
 let pointer=&mut receiver as *mut EbyKDot as usize;
 let value:E=kani::any();let scalar:QM31=kani::any();
 let mut reply=NFC_Reply{words:kani::any(),calls:0,receiver:0,count:99};
 let returned=NFC_push(&mut reply,&mut receiver,value,scalar);returned.unwrap();
 assert_eq!(reply.calls,1);assert_eq!(reply.receiver,pointer);assert_eq!(reply.count,position);
 assert_eq!(receiver.count,position+1);
 let lane:usize=kani::any();kani::assume(lane<8);
 let got=if lane<4{receiver.c0.sums[lane]}else{receiver.c1.sums[lane-4]};
 let expected=reply.words[lane];
 assert_eq!(got,if cfg!(NFC_wrong_receiver_window){expected^1}else{expected});
}
