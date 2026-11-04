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
 for i in 0..8 {kani::assume(limbs[i]<=6*10737418238u64);}
 let lane:usize=kani::any();kani::assume(lane<8);let before=limbs[lane];let selected=sums[lane];
 NFF_fold(sums,&mut limbs);
 let expected=before+(selected&0x7fff_ffff)+(selected>>31);
 assert_eq!(limbs[lane],if cfg!(NFF_wrong_fold){expected^1}else{expected});
 assert!(limbs[lane]<=7*10737418238u64);
}
struct NFF_ChildLog { calls:usize,slots:[usize;4],qptr:[usize;4],gptr:[usize;4],replies:[WideExact;4] }
fn NFF_child(q:&[u8;608],g:&[WideExact;29],slot:usize,log:&mut NFF_ChildLog)->WideExact {
 let at=log.calls;log.calls+=1;log.slots[at]=slot;
 log.qptr[at]=q.as_ptr() as usize;log.gptr[at]=g.as_ptr() as usize;
 log.replies[at]
}
fn NFF_four(q:&[u8],g:&[WideExact;29],log:&mut NFF_ChildLog)->[WideExact;4] {
 let q:&[u8;608]=q[..608].try_into().unwrap();
 [NFF_child(q,g,0,log),NFF_child(q,g,1,log),NFF_child(q,g,2,log),NFF_child(q,g,3,log),]
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

fn NFF_select_tail(q:&[u8;608],g:&[WideExact;29],slot:usize,call:usize)->(WideExact,QM31) {
 match call {
  0 => (g[28],QM31::from_le_bytes(&q[slot*120+104..slot*120+120]).unwrap()),
  1 => {let offset0=480+slot*32+0*16;(g[0+26],QM31::from_le_bytes(&q[offset0..offset0+16]).unwrap())},
  _ => {let offset1=480+slot*32+1*16;(g[1+26],QM31::from_le_bytes(&q[offset1..offset1+16]).unwrap())}
 }
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn tail_argument_window() {
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let call:usize=kani::any();let lane:usize=kani::any();let word:usize=kani::any();
 kani::assume(slot<4 && call<3 && lane<8 && word<4);
 let offset=if call==0{slot*120+104}else{480+slot*32+(call-1)*16};
 for i in 0..4 {let at=offset+4*i;let x=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);kani::assume(x<2147483647);}
 let (value,scalar)=NFF_select_tail(&q,&g,slot,call);
 let coefficient=if call==0{28}else if call==1{26}else{27};
 assert_eq!(value.to_limbs()[lane],g[coefficient].to_limbs()[lane]);
 let words=[scalar.c0.a.0,scalar.c0.b.0,scalar.c1.a.0,scalar.c1.b.0];
 let at=offset+4*word;let expected=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 assert_eq!(words[word],if cfg!(NFF_wrong_tail_arguments){expected^1}else{expected});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn native_inner_range_step() {
 let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=end && end<=26);
 let mut iter=start..end;let returned=iter.next();
 if start<end {assert_eq!(returned,Some(start));assert_eq!(iter.start,start+1);}else{assert_eq!(returned,None);assert_eq!(iter.start,start);}
 assert_eq!(iter.end,if cfg!(NFF_wrong_inner_range){end^1}else{end});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFF_copy::KMX_copy_nonoverlapping)]
fn native_outer_cursor_step() {
 let cursor:usize=kani::any();kani::assume(cursor<=26);
 let mut iter=(cursor..26).step_by(4);
 let first=iter.next();let next=iter.next();
 if cursor<26 {assert_eq!(first,Some(cursor));}else{assert_eq!(first,None);}
 let expected=if cursor+4<26{Some(cursor+4)}else{None};
 assert_eq!(next,if cfg!(NFF_wrong_outer_cursor){Some(99)}else{expected});
}
