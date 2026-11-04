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
// Source-ordered three-call tail after the independently checked source reads.
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFC_copy::KMX_copy_nonoverlapping)]
fn tail_chain_window() {
 let mut receiver=EbyKDot::new();let pointer=&mut receiver as *mut EbyKDot as usize;
 let value:E=kani::any();let scalar:QM31=kani::any();
 let mut a=NFC_Reply{words:kani::any(),calls:0,receiver:0,count:99};
 let mut b=NFC_Reply{words:kani::any(),calls:0,receiver:0,count:99};
 let mut c=NFC_Reply{words:kani::any(),calls:0,receiver:0,count:99};
 let lane:usize=kani::any();kani::assume(lane<8);
 let read=|v:&EbyKDot|if lane<4{v.c0.sums[lane]}else{v.c1.sums[lane-4]};
 assert_eq!(read(&receiver),0);NFC_push(&mut a,&mut receiver,value,scalar).unwrap();
 assert_eq!(read(&receiver),a.words[lane]);NFC_push(&mut b,&mut receiver,value,scalar).unwrap();
 assert_eq!(read(&receiver),b.words[lane]);NFC_push(&mut c,&mut receiver,value,scalar).unwrap();
 assert_eq!(a.receiver,pointer);assert_eq!(b.receiver,pointer);assert_eq!(c.receiver,pointer);
 assert_eq!((a.count,b.count,c.count),(0,1,2));assert_eq!((a.calls,b.calls,c.calls),(1,1,1));
 assert_eq!(receiver.count,3);let expected=c.words[lane];
 assert_eq!(read(&receiver),if cfg!(NFC_wrong_chain_window){expected^1}else{expected});
}
struct NFC_FinishLog { before:[u64;8],count:usize,calls:usize,reply:E }
fn NFC_finish(log:&mut NFC_FinishLog,receiver:EbyKDot)->E {
 log.before=[receiver.c0.sums[0],receiver.c0.sums[1],receiver.c0.sums[2],receiver.c0.sums[3],
  receiver.c1.sums[0],receiver.c1.sums[1],receiver.c1.sums[2],receiver.c1.sums[3]];
 log.count=receiver.count;log.calls+=1;log.reply
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFC_copy::KMX_copy_nonoverlapping)]
fn tail_finish_context() {
 let left:[u64;4]=kani::any();let right:[u64;4]=kani::any();
 let receiver=EbyKDot{c0:Dot{sums:left},c1:Dot{sums:right},count:3};
 let mut log=NFC_FinishLog{before:[0;8],count:99,calls:0,reply:kani::any()};
 let out=NFC_finish(&mut log,receiver);let lane:usize=kani::any();kani::assume(lane<8);
 assert_eq!(log.calls,1);assert_eq!(log.count,3);
 assert_eq!(log.before[lane],if lane<4{left[lane]}else{right[lane-4]});
 let expected=log.reply.to_limbs()[lane];
 assert_eq!(out.to_limbs()[lane],if cfg!(NFC_wrong_finish_context){expected^1}else{expected});
}
struct NFC_AddLog { left:E,right:E,calls:usize,reply:E }
fn NFC_add(log:&mut NFC_AddLog,left:E,right:E)->E {log.left=left;log.right=right;log.calls+=1;log.reply}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFC_copy::KMX_copy_nonoverlapping)]
fn tail_add_context() {
 let left:E=kani::any();let right:E=kani::any();
 let mut log=NFC_AddLog{left:kani::any(),right:kani::any(),calls:0,reply:kani::any()};
 let out=NFC_add(&mut log,left,right);let lane:usize=kani::any();kani::assume(lane<8);
 assert_eq!(log.calls,1);assert_eq!(log.left.to_limbs()[lane],left.to_limbs()[lane]);
 assert_eq!(log.right.to_limbs()[lane],right.to_limbs()[lane]);let expected=log.reply.to_limbs()[lane];
 assert_eq!(out.to_limbs()[lane],if cfg!(NFC_wrong_add_context){expected^1}else{expected});
}
struct NFC_ArgLog {value:E,scalar:QM31,calls:usize}
fn NFC_args(log:&mut NFC_ArgLog,value:E,scalar:QM31) {log.value=value;log.scalar=scalar;log.calls+=1;}
fn NFC_qwords(q:QM31)->[u32;4] {[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFC_copy::KMX_copy_nonoverlapping)]
fn tail_argument_window() {
 let value:E=kani::any();let scalar:QM31=kani::any();
 let mut log=NFC_ArgLog{value:kani::any(),scalar:kani::any(),calls:0};NFC_args(&mut log,value,scalar);
 let lane:usize=kani::any();let qlane:usize=kani::any();kani::assume(lane<8 && qlane<4);
 assert_eq!(log.calls,1);assert_eq!(NFC_qwords(log.scalar)[qlane],NFC_qwords(scalar)[qlane]);
 let expected=value.to_limbs()[lane];
 assert_eq!(log.value.to_limbs()[lane],if cfg!(NFC_wrong_argument_window){expected^1}else{expected});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFC_copy::KMX_copy_nonoverlapping)]
fn tail_readonly_window() {
 let source:[u8;16]=kani::any();let coefficient:E=kani::any();let scalar:QM31=kani::any();
 let at:usize=kani::any();let lane:usize=kani::any();kani::assume(at<16 && lane<8);
 let before_byte=source[at];let before_word=coefficient.to_limbs()[lane];
 let mut receiver=EbyKDot{c0:Dot{sums:kani::any()},c1:Dot{sums:kani::any()},count:kani::any()};
 kani::assume(receiver.count<3);
 let mut reply=NFC_Reply{words:kani::any(),calls:0,receiver:0,count:99};
 NFC_push(&mut reply,&mut receiver,coefficient,scalar).unwrap();
 assert_eq!(coefficient.to_limbs()[lane],before_word);
 assert_eq!(source[at],if cfg!(NFC_wrong_readonly_window){before_byte^1}else{before_byte});
}
struct NFC_FullReply { step:NFC_Reply,args:NFC_ArgLog }
fn NFC_full_push(reply:&mut NFC_FullReply,receiver:&mut EbyKDot,value:E,scalar:QM31) {
 NFC_args(&mut reply.args,value,scalar);NFC_push(&mut reply.step,receiver,value,scalar).unwrap();
}
fn NFC_full_reply()->NFC_FullReply {NFC_FullReply{
 step:NFC_Reply{words:kani::any(),calls:0,receiver:0,count:99},
 args:NFC_ArgLog{value:kani::any(),scalar:kani::any(),calls:0}}}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFC_copy::KMX_copy_nonoverlapping)]
fn tail_chain_finish_add_window() {
 let mut receiver=EbyKDot::new();let pointer=&mut receiver as *mut EbyKDot as usize;
 let value0:E=kani::any();let value1:E=kani::any();let value2:E=kani::any();
 let scalar0:QM31=kani::any();let scalar1:QM31=kani::any();let scalar2:QM31=kani::any();
 let mut a=NFC_full_reply();let mut b=NFC_full_reply();let mut c=NFC_full_reply();
 let lane:usize=kani::any();let qlane:usize=kani::any();kani::assume(lane<8 && qlane<4);
 let read=|v:&EbyKDot|if lane<4{v.c0.sums[lane]}else{v.c1.sums[lane-4]};
 let old0=read(&receiver);NFC_full_push(&mut a,&mut receiver,value0,scalar0);
 let old1=read(&receiver);NFC_full_push(&mut b,&mut receiver,value1,scalar1);
 let old2=read(&receiver);NFC_full_push(&mut c,&mut receiver,value2,scalar2);
 let mut finish=NFC_FinishLog{before:[0;8],count:99,calls:0,reply:kani::any()};
 let tail=NFC_finish(&mut finish,receiver);let head:E=kani::any();
 let mut add=NFC_AddLog{left:kani::any(),right:kani::any(),calls:0,reply:kani::any()};
 let out=NFC_add(&mut add,head,tail);
 assert_eq!((old0,old1,old2),(0,a.step.words[lane],b.step.words[lane]));
 assert_eq!((a.step.receiver,b.step.receiver,c.step.receiver),(pointer,pointer,pointer));
 assert_eq!((a.step.count,b.step.count,c.step.count),(0,1,2));
 assert_eq!((a.step.calls,b.step.calls,c.step.calls),(1,1,1));
 assert_eq!((a.args.calls,b.args.calls,c.args.calls),(1,1,1));
 let observed:usize=kani::any();kani::assume(observed<3);
 let (log,value,scalar)=if observed==0{(&a.args,value0,scalar0)}else if observed==1{(&b.args,value1,scalar1)}else{(&c.args,value2,scalar2)};
 assert_eq!(log.value.to_limbs()[lane],value.to_limbs()[lane]);
 assert_eq!(NFC_qwords(log.scalar)[qlane],NFC_qwords(scalar)[qlane]);
 assert_eq!(finish.count,3);assert_eq!(finish.calls,1);assert_eq!(finish.before[lane],c.step.words[lane]);
 assert_eq!(add.calls,1);assert_eq!(add.left.to_limbs()[lane],head.to_limbs()[lane]);
 assert_eq!(add.right.to_limbs()[lane],finish.reply.to_limbs()[lane]);
 let expected=add.reply.to_limbs()[lane];
 assert_eq!(out.to_limbs()[lane],if cfg!(NFC_wrong_chain_finish_add){expected^1}else{expected});
}
