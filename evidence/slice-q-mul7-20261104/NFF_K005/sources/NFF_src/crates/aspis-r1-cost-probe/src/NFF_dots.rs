use super::*;
const NFF_BOUND:u64=4611686009837453316; // (P-1)^2
struct NFF_Log { replies:[u64;8],left:[u32;8],right:[u32;8],calls:[u8;8] }
fn NFF_product(log:&mut NFF_Log,lane:usize,a:u32,b:u32)->u64 {
 log.left[lane]=a;log.right[lane]=b;log.calls[lane]+=1;log.replies[lane]
}
fn NFF_step(q:&[u8;608],g:&[WideExact;29],slot:usize,term:usize,sums:&mut[u64;8],log:&mut NFF_Log) {
                let scalar = M31::from_le_bytes(
                    q[slot * 120 + term * 4..slot * 120 + term * 4 + 4]
                        .try_into()
                        .unwrap(),
                )
                .unwrap();
                let coefficient = g[term].to_limbs();
                sums[0] += NFF_product(log, 0, coefficient[0], scalar.0);
                sums[1] += NFF_product(log, 1, coefficient[1], scalar.0);
                sums[2] += NFF_product(log, 2, coefficient[2], scalar.0);
                sums[3] += NFF_product(log, 3, coefficient[3], scalar.0);
                sums[4] += NFF_product(log, 4, coefficient[4], scalar.0);
                sums[5] += NFF_product(log, 5, coefficient[5], scalar.0);
                sums[6] += NFF_product(log, 6, coefficient[6], scalar.0);
                sums[7] += NFF_product(log, 7, coefficient[7], scalar.0);
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn main_term_window() {
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && term<26 && lane<8);
 let at=slot*120+term*4;
 let scalar=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(scalar<2147483647);
 let mut sums:[u64;8]=kani::any();let replies:[u64;8]=kani::any();
 for i in 0..8 {kani::assume(sums[i]<=3*NFF_BOUND);kani::assume(replies[i]<=NFF_BOUND);}
 let before=sums[lane];let byte=q[at];let coefficient=g[term].to_limbs()[lane];
 let mut log=NFF_Log{replies,left:[0;8],right:[0;8],calls:[0;8]};
 NFF_step(&q,&g,slot,term,&mut sums,&mut log);
 assert_eq!(log.calls[lane],1);
 assert_eq!(log.left[lane],coefficient);assert_eq!(log.right[lane],scalar);
 assert_eq!(q[at],byte);assert_eq!(g[term].to_limbs()[lane],coefficient);
 let expected=before+replies[lane];
 assert_eq!(sums[lane],if cfg!(NFF_wrong_main_term){expected^1}else{expected});
}

fn NFF_fold(sums:[u64;8],limbs:&mut[u64;8]) {
            limbs[0] += (sums[0] & 0x7fff_ffff) + (sums[0] >> 31);
            limbs[1] += (sums[1] & 0x7fff_ffff) + (sums[1] >> 31);
            limbs[2] += (sums[2] & 0x7fff_ffff) + (sums[2] >> 31);
            limbs[3] += (sums[3] & 0x7fff_ffff) + (sums[3] >> 31);
            limbs[4] += (sums[4] & 0x7fff_ffff) + (sums[4] >> 31);
            limbs[5] += (sums[5] & 0x7fff_ffff) + (sums[5] >> 31);
            limbs[6] += (sums[6] & 0x7fff_ffff) + (sums[6] >> 31);
            limbs[7] += (sums[7] & 0x7fff_ffff) + (sums[7] >> 31);
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn outer_fold_window() {
 let sums:[u64;8]=kani::any();let mut limbs:[u64;8]=kani::any();
 for i in 0..8 {kani::assume(limbs[i]<=6*(1u64<<33));}
 let lane:usize=kani::any();kani::assume(lane<8);let before=limbs[lane];let selected=sums[lane];
 NFF_fold(sums,&mut limbs);
 let expected=before+(selected&0x7fff_ffff)+(selected>>31);
 assert_eq!(limbs[lane],if cfg!(NFF_wrong_fold){expected^1}else{expected});
 assert!(limbs[lane]<=7*(1u64<<33));
}
struct NFF_ChildLog { calls:usize,slots:[usize;4],qptr:[usize;4],gptr:[usize;4],replies:[WideExact;4] }
fn NFF_child(q:&[u8;608],g:&[WideExact;29],slot:usize,log:&mut NFF_ChildLog)->WideExact {
 let at=log.calls;log.calls+=1;log.slots[at]=slot;
 log.qptr[at]=q.as_ptr() as usize;log.gptr[at]=g.as_ptr() as usize;
 log.replies[at]
}
fn NFF_four(q:&[u8],g:&[WideExact;29],log:&mut NFF_ChildLog)->[WideExact;4] {
 let q:&[u8;608]=q[..608].try_into().unwrap();
 [NFF_child(q,g,0,log),NFF_child(q,g,1,log),NFF_child(q,g,2,log),NFF_child(q,g,3,log)]
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn wrapper_calls_window() {
 let q:[u8;609]=kani::any();let g:[WideExact;29]=kani::any();
 let replies:[WideExact;4]=kani::any();
 let mut log=NFF_ChildLog{calls:0,slots:[99;4],qptr:[0;4],gptr:[0;4],replies};
 let out=NFF_four(&q,&g,&mut log);
 let at:usize=kani::any();let lane:usize=kani::any();kani::assume(at<4 && lane<8);
 assert_eq!(log.calls,4);assert_eq!(log.slots[at],at);
 assert_eq!(log.qptr[at],q.as_ptr() as usize);assert_eq!(log.gptr[at],g.as_ptr() as usize);
 let expected=replies[at].to_limbs()[lane];
 assert_eq!(out[at].to_limbs()[lane],if cfg!(NFF_wrong_wrapper){expected^1}else{expected});
}
