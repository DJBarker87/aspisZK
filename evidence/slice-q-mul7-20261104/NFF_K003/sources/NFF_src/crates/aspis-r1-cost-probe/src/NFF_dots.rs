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
