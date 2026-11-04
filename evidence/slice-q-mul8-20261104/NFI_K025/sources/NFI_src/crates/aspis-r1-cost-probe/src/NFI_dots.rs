use super::*;
const NFI_BOUND:u64=4611686009837453316; // (P-1)^2
struct NFI_Log { replies:[u64;8],left:[u32;8],right:[u32;8],calls:[u8;8],order:[usize;8],next:usize }
fn NFI_product(log:&mut NFI_Log,lane:usize,a:u32,b:u32)->u64 {
 log.order[log.next]=lane;log.next+=1;
 log.left[lane]=a;log.right[lane]=b;log.calls[lane]+=1;log.replies[lane]
}
fn NFI_step(q:&[u8;608],g:&[WideExact;29],slot:usize,term:usize,sums:&mut[u64;8],log:&mut NFI_Log) {
                let scalar = M31::from_le_bytes(
                    q[slot * 120 + term * 4..slot * 120 + term * 4 + 4]
                        .try_into()
                        .unwrap(),
                )
                .unwrap();
                let coefficient = g[term].to_limbs();
                sums[0] += NFI_product(log, 0, coefficient[0], scalar.0);
                sums[1] += NFI_product(log, 1, coefficient[1], scalar.0);
                sums[2] += NFI_product(log, 2, coefficient[2], scalar.0);
                sums[3] += NFI_product(log, 3, coefficient[3], scalar.0);
                sums[4] += NFI_product(log, 4, coefficient[4], scalar.0);
                sums[5] += NFI_product(log, 5, coefficient[5], scalar.0);
                sums[6] += NFI_product(log, 6, coefficient[6], scalar.0);
                sums[7] += NFI_product(log, 7, coefficient[7], scalar.0);
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
fn main_term_window() {
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && term<26 && lane<8);
 let at=slot*120+term*4;
 let scalar=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(scalar<2147483647);
 let mut sums:[u64;8]=kani::any();let replies:[u64;8]=kani::any();
 for i in 0..8 {kani::assume(sums[i]<=3*NFI_BOUND);kani::assume(replies[i]<=NFI_BOUND);}
 let before=sums[lane];let byte=q[at];let coefficient=g[term].to_limbs()[lane];
 let mut log=NFI_Log{replies,left:[0;8],right:[0;8],calls:[0;8],order:[99;8],next:0};
 NFI_step(&q,&g,slot,term,&mut sums,&mut log);
 assert_eq!(log.next,8);assert_eq!(log.order[lane],lane);
 assert_eq!(log.calls[lane],1);
 assert_eq!(log.left[lane],coefficient);assert_eq!(log.right[lane],scalar);
 assert_eq!(q[at],byte);assert_eq!(g[term].to_limbs()[lane],coefficient);
 let expected=before+replies[lane];
 assert_eq!(sums[lane],if cfg!(NFI_wrong_main_term){expected^1}else{expected});
}

fn NFI_fold(sums:[u64;8],limbs:&mut[u64;8]) {
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
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
fn outer_fold_window() {
 let sums:[u64;8]=kani::any();let mut limbs:[u64;8]=kani::any();
 for i in 0..8 {kani::assume(limbs[i]<=6*10737418238u64);}
 let lane:usize=kani::any();kani::assume(lane<8);let before=limbs[lane];let selected=sums[lane];
 NFI_fold(sums,&mut limbs);
 let expected=before+(selected&0x7fff_ffff)+(selected>>31);
 assert_eq!(limbs[lane],if cfg!(NFI_wrong_fold){expected^1}else{expected});
 assert!(limbs[lane]<=7*10737418238u64);
}
struct NFI_ChildLog { calls:usize,slots:[usize;4],qptr:[usize;4],gptr:[usize;4],replies:[WideExact;4] }
fn NFI_child(q:&[u8;608],g:&[WideExact;29],slot:usize,log:&mut NFI_ChildLog)->WideExact {
 let at=log.calls;log.calls+=1;log.slots[at]=slot;
 log.qptr[at]=q.as_ptr() as usize;log.gptr[at]=g.as_ptr() as usize;
 log.replies[at]
}
fn NFI_four(q:&[u8],g:&[WideExact;29],log:&mut NFI_ChildLog)->[WideExact;4] {
 let q:&[u8;608]=q[..608].try_into().unwrap();
 [NFI_child(q,g,0,log),NFI_child(q,g,1,log),NFI_child(q,g,2,log),NFI_child(q,g,3,log),]
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
fn wrapper_calls_window() {
 let q:[u8;609]=kani::any();let g:[WideExact;29]=kani::any();
 let replies:[WideExact;4]=kani::any();
 let mut log=NFI_ChildLog{calls:0,slots:[99;4],qptr:[0;4],gptr:[0;4],replies};
 let out=NFI_four(&q,&g,&mut log);
 let at:usize=kani::any();let lane:usize=kani::any();kani::assume(at<4 && lane<8);
 assert_eq!(log.calls,4);assert_eq!(log.slots[at],at);
 assert_eq!(log.qptr[at],q.as_ptr() as usize);assert_eq!(log.gptr[at],g.as_ptr() as usize);
 let expected=replies[at].to_limbs()[lane];
 assert_eq!(out[at].to_limbs()[lane],if cfg!(NFI_wrong_wrapper){expected^1}else{expected});
}

// Adjacent native cuts share the actual records. No complete-loop harness.
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
fn entry_to_inner_frame(){
 let limbs=[0u64;WideExact::LIMB_COUNT];
 let mut outer=(0..26).step_by(4);let start=outer.next().unwrap();
 let sums=[0u64;WideExact::LIMB_COUNT];
 let inner=start..core::cmp::min(start+4,26);
 let lane:usize=kani::any();kani::assume(lane<8);
 assert_eq!(limbs[lane],0);assert_eq!(sums[lane],0);assert_eq!(inner.end,4);
 assert_eq!(inner.start,if cfg!(NFI_wrong_entry){1}else{0});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
fn cursor_to_product_frame(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let start:usize=kani::any();let end:usize=kani::any();
 let lane:usize=kani::any();let observed:usize=kani::any();let gi:usize=kani::any();let gl:usize=kani::any();
 kani::assume(slot<4 && start<end && end<=26 && lane<8 && observed<608 && gi<29 && gl<8);
 let at=slot*120+start*4;let scalar=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(scalar<2147483647);
 let mut sums:[u64;8]=kani::any();let replies:[u64;8]=kani::any();
 for i in 0..8{kani::assume(sums[i]<=3*NFI_BOUND);kani::assume(replies[i]<=NFI_BOUND);}
 let before=sums[lane];let byte=q[observed];let coeff=g[gi].to_limbs()[gl];
 let qp=q.as_ptr() as usize;let gp=g.as_ptr() as usize;
 let mut iter=start..end;let term=iter.next().unwrap();
 let mut log=NFI_Log{replies,left:[0;8],right:[0;8],calls:[0;8],order:[99;8],next:0};
 NFI_step(&q,&g,slot,term,&mut sums,&mut log);
 assert_eq!(iter.start,start+1);assert_eq!(iter.end,end);
 assert_eq!(log.left[lane],g[start].to_limbs()[lane]);assert_eq!(log.right[lane],scalar);assert_eq!(log.calls[lane],1);
 assert_eq!(q.as_ptr() as usize,qp);assert_eq!(g.as_ptr() as usize,gp);
 assert_eq!(q[observed],byte);assert_eq!(g[gi].to_limbs()[gl],coeff);
 assert_eq!(sums[lane],if cfg!(NFI_wrong_cursor_product){(before+replies[lane])^1}else{before+replies[lane]});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
fn exhausted_inner_to_fold_frame(){
 let cursor:usize=kani::any();kani::assume(cursor<=26);
 let mut iter=cursor..cursor;
 let sums:[u64;8]=kani::any();let mut limbs:[u64;8]=kani::any();
 for i in 0..8{kani::assume(limbs[i]<=6*10737418238u64);}
 let lane:usize=kani::any();kani::assume(lane<8);let before=limbs[lane];
 assert_eq!(iter.next(),None);
 NFI_fold(sums,&mut limbs);
 assert_eq!(iter.start,cursor);assert_eq!(iter.end,cursor);
 let expected=before+(sums[lane]&0x7fffffff)+(sums[lane]>>31);
 assert_eq!(limbs[lane],if cfg!(NFI_wrong_exhaust_fold){expected^1}else{expected});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFI_copy::KMX_copy_nonoverlapping)]
fn fold_to_next_outer_frame(){
 let start:usize=kani::any();kani::assume(start<26 && start%4==0);
 let sums:[u64;8]=kani::any();let mut limbs:[u64;8]=kani::any();
 for i in 0..8{kani::assume(limbs[i]<=6*10737418238u64);}
 let lane:usize=kani::any();kani::assume(lane<8);let before=limbs[lane];
 let mut outer=(start..26).step_by(4);assert_eq!(outer.next(),Some(start));
 NFI_fold(sums,&mut limbs);
 let after=limbs[lane];let next=outer.next();
 assert_eq!(after,before+(sums[lane]&0x7fffffff)+(sums[lane]>>31));
 let expected=if start+4<26{Some(start+4)}else{None};
 assert_eq!(next,if cfg!(NFI_wrong_fold_next){Some(99)}else{expected});
 assert_eq!(limbs[lane],after);
}
