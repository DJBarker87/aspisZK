use super::*;
use super::super::{EbyKDot,E,QM31};
struct NFF_RawLog { replies:[u64;16],left:[u64;16],right:[u64;16],order:[usize;16],calls:usize }
fn NFF_product(log:&mut NFF_RawLog,at:usize,a:u64,b:u64)->u64 {
 log.order[log.calls]=at;log.calls+=1;log.left[at]=a;log.right[at]=b;log.replies[at]
}
fn NFF_raw(left:Q,rhs:Q,log:&mut NFF_RawLog)->[u64;4] {

            let [a,b,c,d]=[u64::from(left.0[0]),u64::from(left.0[1]),u64::from(left.0[2]),u64::from(left.0[3])];
            let [e,f,g,h]=[u64::from(rhs.0[0]),u64::from(rhs.0[1]),u64::from(rhs.0[2]),u64::from(rhs.0[3])];
            const PP:u64=(P as u64)*(P as u64);
            let partial=|x:u64|(x&u64::from(P)).wrapping_add(x>>31u32);
            let u=partial((NFF_product(log,0,c,g)).wrapping_add(PP).wrapping_sub(NFF_product(log,1,d,h)));
            let v=partial((NFF_product(log,2,c,h)).wrapping_add(NFF_product(log,3,d,g)));
            [(NFF_product(log,4,a,e)).wrapping_add(PP).wrapping_sub(NFF_product(log,5,b,f)).wrapping_add(2*u).wrapping_add(3*u64::from(P)).wrapping_sub(v),
             (NFF_product(log,6,a,f)).wrapping_add(NFF_product(log,7,b,e)).wrapping_add(u).wrapping_add(2*v),
             (NFF_product(log,8,a,g)).wrapping_add(NFF_product(log,9,c,e)).wrapping_add(2*PP).wrapping_sub(NFF_product(log,10,b,h)).wrapping_sub(NFF_product(log,11,d,f)),
             (NFF_product(log,12,a,h)).wrapping_add(NFF_product(log,13,b,g)).wrapping_add(NFF_product(log,14,c,f)).wrapping_add(NFF_product(log,15,d,e))]
        
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn raw_operand_window() {
 let left:[u32;4]=kani::any();let right:[u32;4]=kani::any();
 for i in 0..4 {kani::assume(left[i]<P && right[i]<P);}
 let replies:[u64;16]=kani::any();for i in 0..16 {kani::assume(replies[i]<=4611686009837453316);}
 let mut log=NFF_RawLog{replies,left:[0;16],right:[0;16],order:[99;16],calls:0};
 let out=NFF_raw(Q(left),Q(right),&mut log);
 let at:usize=kani::any();kani::assume(at<16);
 let pairs=[(2, 2), (3, 3), (2, 3), (3, 2), (0, 0), (1, 1), (0, 1), (1, 0), (0, 2), (2, 0), (1, 3), (3, 1), (0, 3), (1, 2), (2, 1), (3, 0)];
 assert_eq!(log.calls,16);assert_eq!(log.order[at],at);
 assert_eq!(log.left[at],u64::from(left[pairs[at].0]));
 let expected=u64::from(right[pairs[at].1]);
 assert_eq!(log.right[at],if cfg!(NFF_wrong_raw_operand){expected^1}else{expected});
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
fn NFF_dot_step(dot:&mut Dot,raw:&[u64;4],j:usize) {
 dot.sums[j]=dot.sums[j].wrapping_add((raw[j]&u64::from(P)).wrapping_add(raw[j]>>31u32));
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn private_push_step_window() {
 let old:[u64;4]=kani::any();let raw:[u64;4]=kani::any();let j:usize=kani::any();let observed:usize=kani::any();
 kani::assume(j<4 && observed<4);let mut dot=Dot{sums:old};NFF_dot_step(&mut dot,&raw,j);
 let expected=if observed==j{old[j].wrapping_add((raw[j]&u64::from(P)).wrapping_add(raw[j]>>31))}else{old[observed]};
 assert_eq!(dot.sums[observed],if cfg!(NFF_wrong_private_step){expected^1}else{expected});
}
