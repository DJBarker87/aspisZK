use crate::fast_pairing::canonical;
use super::*;
use super::super::{EbyKDot,E,QM31,MAX_TERMS,checked_q};
struct NFM_RawLog { replies:[u64;16],left:[u64;16],right:[u64;16],order:[usize;16],calls:usize }
fn NFM_product(log:&mut NFM_RawLog,at:usize,a:u64,b:u64)->u64 {
 log.order[log.calls]=at;log.calls+=1;log.left[at]=a;log.right[at]=b;log.replies[at]
}
fn NFM_raw(left:Q,rhs:Q,log:&mut NFM_RawLog)->[u64;4] {

            let [a,b,c,d]=[u64::from(left.0[0]),u64::from(left.0[1]),u64::from(left.0[2]),u64::from(left.0[3])];
            let [e,f,g,h]=[u64::from(rhs.0[0]),u64::from(rhs.0[1]),u64::from(rhs.0[2]),u64::from(rhs.0[3])];
            const PP:u64=(P as u64)*(P as u64);
            let partial=|x:u64|(x&u64::from(P)).wrapping_add(x>>31u32);
            let u=partial((NFM_product(log,0,c,g)).wrapping_add(PP).wrapping_sub(NFM_product(log,1,d,h)));
            let v=partial((NFM_product(log,2,c,h)).wrapping_add(NFM_product(log,3,d,g)));
            [(NFM_product(log,4,a,e)).wrapping_add(PP).wrapping_sub(NFM_product(log,5,b,f)).wrapping_add(2*u).wrapping_add(3*u64::from(P)).wrapping_sub(v),
             (NFM_product(log,6,a,f)).wrapping_add(NFM_product(log,7,b,e)).wrapping_add(u).wrapping_add(2*v),
             (NFM_product(log,8,a,g)).wrapping_add(NFM_product(log,9,c,e)).wrapping_add(2*PP).wrapping_sub(NFM_product(log,10,b,h)).wrapping_sub(NFM_product(log,11,d,f)),
             (NFM_product(log,12,a,h)).wrapping_add(NFM_product(log,13,b,g)).wrapping_add(NFM_product(log,14,c,f)).wrapping_add(NFM_product(log,15,d,e))]
        
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn raw_operand_window() {
 let left:[u32;4]=kani::any();let right:[u32;4]=kani::any();
 for i in 0..4 {kani::assume(left[i]<P && right[i]<P);}
 let replies:[u64;16]=kani::any();for i in 0..16 {kani::assume(replies[i]<=4611686009837453316);}
 let mut log=NFM_RawLog{replies,left:[0;16],right:[0;16],order:[99;16],calls:0};
 let out=NFM_raw(Q(left),Q(right),&mut log);
 let at:usize=kani::any();kani::assume(at<16);
 let pairs=[(2, 2), (3, 3), (2, 3), (3, 2), (0, 0), (1, 1), (0, 1), (1, 0), (0, 2), (2, 0), (1, 3), (3, 1), (0, 3), (1, 2), (2, 1), (3, 0)];
 assert_eq!(log.calls,16);assert_eq!(log.order[at],at);
 assert_eq!(log.left[at],u64::from(left[pairs[at].0]));
 let expected=u64::from(right[pairs[at].1]);
 assert_eq!(log.right[at],if cfg!(NFM_wrong_raw_operand){expected^1}else{expected});
 // The result is computed from the SAME local product replies, never picked afterwards.
 const PP:u64=4611686014132420609;
 let fold=|x:u64|(x&0x7fffffff).wrapping_add(x>>31);
 let u=fold(replies[0].wrapping_add(PP).wrapping_sub(replies[1]));
 let v=fold(replies[2].wrapping_add(replies[3]));
 let expected=[replies[4].wrapping_add(PP).wrapping_sub(replies[5]).wrapping_add(2*u).wrapping_add(3*u64::from(P)).wrapping_sub(v),
 replies[6].wrapping_add(replies[7]).wrapping_add(u).wrapping_add(2*v),
 replies[8].wrapping_add(replies[9]).wrapping_add(2*PP).wrapping_sub(replies[10]).wrapping_sub(replies[11]),
 replies[12].wrapping_add(replies[13]).wrapping_add(replies[14]).wrapping_add(replies[15])];
 let lane:usize=kani::any();kani::assume(lane<4);assert_eq!(out[lane],expected[lane]);
}
fn NFM_dot_step(dot:&mut Dot,raw:&[u64;4],j:usize) {
 dot.sums[j]=dot.sums[j].wrapping_add((raw[j]&u64::from(P)).wrapping_add(raw[j]>>31u32));
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn private_push_step_window() {
 let old:[u64;4]=kani::any();let raw:[u64;4]=kani::any();let j:usize=kani::any();let observed:usize=kani::any();
 kani::assume(j<4 && observed<4);let mut dot=Dot{sums:old};NFM_dot_step(&mut dot,&raw,j);
 let expected=if observed==j{old[j].wrapping_add((raw[j]&u64::from(P)).wrapping_add(raw[j]>>31))}else{old[observed]};
 assert_eq!(dot.sums[observed],if cfg!(NFM_wrong_private_step){expected^1}else{expected});
}

struct NFM_PublicLog { calls:usize,half:[usize;2],receiver:[usize;2],before:[[u64;4];2],left:[[u32;4];2],right:[[u32;4];2],replies:[[u64;4];2] }
fn NFM_private_push(log:&mut NFM_PublicLog,half:usize,dot:&mut Dot,a:Q,b:Q) {
 let at=log.calls;log.calls+=1;log.half[at]=half;
 log.receiver[at]=dot as *mut Dot as usize;log.before[at]=dot.sums;
 log.left[at]=a.0;log.right[at]=b.0;dot.sums=log.replies[at];
}
fn NFM_public_push(receiver:&mut EbyKDot,value:E,scalar:QM31,log:&mut NFM_PublicLog)->Result<(),()> {

        if receiver.count >= MAX_TERMS { return Err(()); }
        let [value_c0,value_c1] = canonical::Q::from_wide(value);
        let scalar = checked_q(scalar)?;
        NFM_private_push(log,0,&mut receiver.c0,value_c0,scalar);
        NFM_private_push(log,1,&mut receiver.c1,value_c1,scalar);
        receiver.count += 1;
        Ok(())
    
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn public_push_context() {
 let mut receiver=EbyKDot{c0:Dot{sums:kani::any()},c1:Dot{sums:kani::any()},count:kani::any()};
 let count=receiver.count;let old=[receiver.c0.sums,receiver.c1.sums];
 let pointer=[&mut receiver.c0 as *mut Dot as usize,&mut receiver.c1 as *mut Dot as usize];
 let value:E=kani::any();let scalar:QM31=kani::any();let limbs=value.to_limbs();
 let q=super::super::limbs_of(scalar);
 let valid=q[0]<P && q[1]<P && q[2]<P && q[3]<P;
 let mut log=NFM_PublicLog{calls:0,half:[99;2],receiver:[0;2],before:[[0;4];2],left:[[0;4];2],right:[[0;4];2],replies:kani::any()};
 let returned=NFM_public_push(&mut receiver,value,scalar,&mut log);
 let half:usize=kani::any();let lane:usize=kani::any();kani::assume(half<2 && lane<4);
 if count>=4096 || !valid {
  assert!(returned.is_err());assert_eq!(log.calls,0);assert_eq!(receiver.count,count);
  let observed=if half==0{receiver.c0.sums[lane]}else{receiver.c1.sums[lane]};
  assert_eq!(observed,old[half][lane]);
 } else {
  assert!(returned.is_ok());assert_eq!(log.calls,2);assert_eq!(receiver.count,count+1);
  assert_eq!(log.half[half],half);assert_eq!(log.receiver[half],pointer[half]);
  assert_eq!(log.before[half][lane],old[half][lane]);
  assert_eq!(log.left[half][lane],limbs[half*4+lane]);assert_eq!(log.right[half][lane],q[lane]);
  let observed=if half==0{receiver.c0.sums[lane]}else{receiver.c1.sums[lane]};
  let expected=log.replies[half][lane];
  assert_eq!(observed,if cfg!(NFM_wrong_public_push){expected^1}else{expected});
 }
}

fn NFM_log()->NFM_PublicLog {NFM_PublicLog{calls:0,half:[99;2],receiver:[0;2],before:[[0;4];2],left:[[0;4];2],right:[[0;4];2],replies:kani::any()}}
fn NFM_tail_chain(values:[E;3],scalars:[QM31;3],logs:&mut[NFM_PublicLog;3])->EbyKDot {
 let mut tail=EbyKDot::new();
 NFM_public_push(&mut tail,values[0],scalars[0],&mut logs[0]).unwrap();
 NFM_public_push(&mut tail,values[1],scalars[1],&mut logs[1]).unwrap();
 NFM_public_push(&mut tail,values[2],scalars[2],&mut logs[2]).unwrap();tail
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn tail_chain_window() {
 let values:[E;3]=kani::any();let scalars:[QM31;3]=kani::any();
 for scalar in scalars {for word in super::super::limbs_of(scalar){kani::assume(word<P);}}
 let mut logs=[NFM_log(),NFM_log(),NFM_log()];let tail=NFM_tail_chain(values,scalars,&mut logs);
 let call:usize=kani::any();let half:usize=kani::any();let lane:usize=kani::any();
 kani::assume(call<3 && half<2 && lane<4);
 assert_eq!(tail.count,3);assert_eq!((logs[0].calls,logs[1].calls,logs[2].calls),(2,2,2));
 assert_eq!(logs[call].left[half][lane],values[call].to_limbs()[half*4+lane]);
 assert_eq!(logs[call].right[half][lane],super::super::limbs_of(scalars[call])[lane]);
 let before=if call==0{0}else{logs[call-1].replies[half][lane]};
 assert_eq!(logs[call].before[half][lane],before);
 let observed=if half==0{tail.c0.sums[lane]}else{tail.c1.sums[lane]};
 let expected=logs[2].replies[half][lane];
 assert_eq!(observed,if cfg!(NFM_wrong_tail_chain){expected^1}else{expected});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn tail_selected_finish_add() {
 let old:[u64;8]=kani::any();let count:usize=kani::any();let head:E=kani::any();
 for word in head.to_limbs(){kani::assume(word<P);}
 let receiver=EbyKDot{c0:Dot{sums:[old[0],old[1],old[2],old[3]]},c1:Dot{sums:[old[4],old[5],old[6],old[7]]},count};
 let out=head.add(receiver.finish());
 let lane:usize=kani::any();kani::assume(lane<8);
 let sum=head.to_limbs()[lane]+reduce(old[lane]);let expected=if sum>=P{sum-P}else{sum};
 assert_eq!(out.to_limbs()[lane],if cfg!(NFM_wrong_tail_finish_add){expected^1}else{expected});
 assert!(out.to_limbs()[lane]<P);
}
