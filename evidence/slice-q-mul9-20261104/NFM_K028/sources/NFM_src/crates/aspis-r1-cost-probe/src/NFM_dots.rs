use super::*;
const NFM_BOUND:u64=4611686009837453316; // (P-1)^2
struct NFM_Log { replies:[u64;8],left:[u32;8],right:[u32;8],calls:[u8;8],order:[usize;8],next:usize }
fn NFM_product(log:&mut NFM_Log,lane:usize,a:u32,b:u32)->u64 {
 log.order[log.next]=lane;log.next+=1;
 log.left[lane]=a;log.right[lane]=b;log.calls[lane]+=1;log.replies[lane]
}
fn NFM_step(q:&[u8;608],g:&[WideExact;29],slot:usize,term:usize,sums:&mut[u64;8],log:&mut NFM_Log) {
                let scalar = M31::from_le_bytes(
                    q[slot * 120 + term * 4..slot * 120 + term * 4 + 4]
                        .try_into()
                        .unwrap(),
                )
                .unwrap();
                let coefficient = g[term].to_limbs();
                sums[0] += NFM_product(log, 0, coefficient[0], scalar.0);
                sums[1] += NFM_product(log, 1, coefficient[1], scalar.0);
                sums[2] += NFM_product(log, 2, coefficient[2], scalar.0);
                sums[3] += NFM_product(log, 3, coefficient[3], scalar.0);
                sums[4] += NFM_product(log, 4, coefficient[4], scalar.0);
                sums[5] += NFM_product(log, 5, coefficient[5], scalar.0);
                sums[6] += NFM_product(log, 6, coefficient[6], scalar.0);
                sums[7] += NFM_product(log, 7, coefficient[7], scalar.0);
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn main_term_window() {
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && term<26 && lane<8);
 let at=slot*120+term*4;
 let scalar=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(scalar<2147483647);
 let mut sums:[u64;8]=kani::any();let replies:[u64;8]=kani::any();
 for i in 0..8 {kani::assume(sums[i]<=3*NFM_BOUND);kani::assume(replies[i]<=NFM_BOUND);}
 let before=sums[lane];let byte=q[at];let coefficient=g[term].to_limbs()[lane];
 let mut log=NFM_Log{replies,left:[0;8],right:[0;8],calls:[0;8],order:[99;8],next:0};
 NFM_step(&q,&g,slot,term,&mut sums,&mut log);
 assert_eq!(log.next,8);assert_eq!(log.order[lane],lane);
 assert_eq!(log.calls[lane],1);
 assert_eq!(log.left[lane],coefficient);assert_eq!(log.right[lane],scalar);
 assert_eq!(q[at],byte);assert_eq!(g[term].to_limbs()[lane],coefficient);
 let expected=before+replies[lane];
 assert_eq!(sums[lane],if cfg!(NFM_wrong_main_term){expected^1}else{expected});
}

fn NFM_fold(sums:[u64;8],limbs:&mut[u64;8]) {
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
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn outer_fold_window() {
 let sums:[u64;8]=kani::any();let mut limbs:[u64;8]=kani::any();
 for i in 0..8 {kani::assume(limbs[i]<=6*10737418238u64);}
 let lane:usize=kani::any();kani::assume(lane<8);let before=limbs[lane];let selected=sums[lane];
 NFM_fold(sums,&mut limbs);
 let expected=before+(selected&0x7fff_ffff)+(selected>>31);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_fold){expected^1}else{expected});
 assert!(limbs[lane]<=7*10737418238u64);
}
struct NFM_ChildLog { calls:usize,slots:[usize;4],qptr:[usize;4],gptr:[usize;4],replies:[WideExact;4] }
fn NFM_child(q:&[u8;608],g:&[WideExact;29],slot:usize,log:&mut NFM_ChildLog)->WideExact {
 let at=log.calls;log.calls+=1;log.slots[at]=slot;
 log.qptr[at]=q.as_ptr() as usize;log.gptr[at]=g.as_ptr() as usize;
 log.replies[at]
}
fn NFM_four(q:&[u8],g:&[WideExact;29],log:&mut NFM_ChildLog)->[WideExact;4] {
 let q:&[u8;608]=q[..608].try_into().unwrap();
 [NFM_child(q,g,0,log),NFM_child(q,g,1,log),NFM_child(q,g,2,log),NFM_child(q,g,3,log),]
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn wrapper_calls_window() {
 let q:[u8;609]=kani::any();let g:[WideExact;29]=kani::any();
 let replies:[WideExact;4]=kani::any();
 let mut log=NFM_ChildLog{calls:0,slots:[99;4],qptr:[0;4],gptr:[0;4],replies};
 let out=NFM_four(&q,&g,&mut log);
 let at:usize=kani::any();let lane:usize=kani::any();kani::assume(at<4 && lane<8);
 assert_eq!(log.calls,4);assert_eq!(log.slots[at],at);
 assert_eq!(log.qptr[at],q.as_ptr() as usize);assert_eq!(log.gptr[at],g.as_ptr() as usize);
 let expected=replies[at].to_limbs()[lane];
 assert_eq!(out[at].to_limbs()[lane],if cfg!(NFM_wrong_wrapper){expected^1}else{expected});
}

struct NFM_ControlLog { pairs:[(usize,usize);26], starts:[usize;7], terms:usize, cuts:usize }
fn NFM_record(log:&mut NFM_ControlLog,start:usize,term:usize){
 log.pairs[log.terms]=(start,term);log.terms+=1;
}
fn NFM_control(log:&mut NFM_ControlLog){
for start in (0..26).step_by(4) {
 log.starts[log.cuts]=start; log.cuts+=1;
 for term in start..core::cmp::min(start + 4, 26) {
 NFM_record(log,start,term);
 }
 }
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn control_trace(){
 let mut log=NFM_ControlLog{pairs:[(99,99);26],starts:[99;7],terms:0,cuts:0};
 NFM_control(&mut log);
 let i:usize=kani::any();kani::assume(i<26);
 let j:usize=kani::any();kani::assume(j<7);
 assert_eq!(log.terms,26);assert_eq!(log.cuts,7);
 assert_eq!(log.starts[j],j*4);
 assert_eq!(log.pairs[i],if cfg!(NFM_wrong_control){((i/4)*4,i+1)}else{((i/4)*4,i)});
}

struct NFM_WindowLog { replies:[[u64;8];4], left:[[u32;8];4], right:[u32;4], order:[usize;32], calls:usize }
fn NFM_window_product(log:&mut NFM_WindowLog,offset:usize,lane:usize,a:u32,b:u32)->u64{
 log.order[log.calls]=offset*8+lane;log.calls+=1;
 log.left[offset][lane]=a;log.right[offset]=b;log.replies[offset][lane]
}
fn NFM_window_term(q:&[u8;608],g:&[WideExact;29],slot:usize,term:usize,offset:usize,sums:&mut[u64;8],log:&mut NFM_WindowLog){
                let scalar = M31::from_le_bytes(
                    q[slot * 120 + term * 4..slot * 120 + term * 4 + 4]
                        .try_into()
                        .unwrap(),
                )
                .unwrap();
                let coefficient = g[term].to_limbs();
                sums[0] += NFM_window_product(log,offset,0, coefficient[0], scalar.0);
                sums[1] += NFM_window_product(log,offset,1, coefficient[1], scalar.0);
                sums[2] += NFM_window_product(log,offset,2, coefficient[2], scalar.0);
                sums[3] += NFM_window_product(log,offset,3, coefficient[3], scalar.0);
                sums[4] += NFM_window_product(log,offset,4, coefficient[4], scalar.0);
                sums[5] += NFM_window_product(log,offset,5, coefficient[5], scalar.0);
                sums[6] += NFM_window_product(log,offset,6, coefficient[6], scalar.0);
                sums[7] += NFM_window_product(log,offset,7, coefficient[7], scalar.0);
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn window_0(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);
 let mut limbs:[u64;8]=kani::any();let mut sums:[u64;8]=kani::any();
 let replies:[[u64;8];4]=kani::any();let lane:usize=kani::any();kani::assume(lane<8);
 for j in 0..8{kani::assume(limbs[j]<=6*10737418238u64);kani::assume(sums[j]<=0*NFM_BOUND);}
 for off in 0..4{
  let at=slot*120+(0+off)*4;
  kani::assume(u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])<2147483647);
  for j in 0..8{kani::assume(replies[off][j]<=NFM_BOUND);}
 }
 let old_s=sums[lane];let old_l=limbs[lane];
 let mut log=NFM_WindowLog{replies,left:[[0;8];4],right:[0;4],order:[99;32],calls:0};
 for term in 0..core::cmp::min(0+4,26){
  NFM_window_term(&q,&g,slot,term,term-0,&mut sums,&mut log);
 }
 let mut expected=old_s;
 for off in 0..4{
  expected+=replies[off][lane];
  let at=slot*120+(0+off)*4;
  assert_eq!(log.left[off][lane],g[0+off].to_limbs()[lane]);
  assert_eq!(log.right[off],u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]));
  assert_eq!(log.order[off*8+lane],off*8+lane);
 }
 assert_eq!(log.calls,4*8);assert_eq!(sums[lane],expected);
 NFM_fold(sums,&mut limbs);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_window_0){(old_l+(expected&0x7fffffff)+(expected>>31))^1}else{old_l+(expected&0x7fffffff)+(expected>>31)});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn window_1(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);
 let mut limbs:[u64;8]=kani::any();let mut sums:[u64;8]=kani::any();
 let replies:[[u64;8];4]=kani::any();let lane:usize=kani::any();kani::assume(lane<8);
 for j in 0..8{kani::assume(limbs[j]<=6*10737418238u64);kani::assume(sums[j]<=0*NFM_BOUND);}
 for off in 0..4{
  let at=slot*120+(4+off)*4;
  kani::assume(u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])<2147483647);
  for j in 0..8{kani::assume(replies[off][j]<=NFM_BOUND);}
 }
 let old_s=sums[lane];let old_l=limbs[lane];
 let mut log=NFM_WindowLog{replies,left:[[0;8];4],right:[0;4],order:[99;32],calls:0};
 for term in 4..core::cmp::min(4+4,26){
  NFM_window_term(&q,&g,slot,term,term-4,&mut sums,&mut log);
 }
 let mut expected=old_s;
 for off in 0..4{
  expected+=replies[off][lane];
  let at=slot*120+(4+off)*4;
  assert_eq!(log.left[off][lane],g[4+off].to_limbs()[lane]);
  assert_eq!(log.right[off],u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]));
  assert_eq!(log.order[off*8+lane],off*8+lane);
 }
 assert_eq!(log.calls,4*8);assert_eq!(sums[lane],expected);
 NFM_fold(sums,&mut limbs);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_window_1){(old_l+(expected&0x7fffffff)+(expected>>31))^1}else{old_l+(expected&0x7fffffff)+(expected>>31)});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn window_2(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);
 let mut limbs:[u64;8]=kani::any();let mut sums:[u64;8]=kani::any();
 let replies:[[u64;8];4]=kani::any();let lane:usize=kani::any();kani::assume(lane<8);
 for j in 0..8{kani::assume(limbs[j]<=6*10737418238u64);kani::assume(sums[j]<=0*NFM_BOUND);}
 for off in 0..4{
  let at=slot*120+(8+off)*4;
  kani::assume(u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])<2147483647);
  for j in 0..8{kani::assume(replies[off][j]<=NFM_BOUND);}
 }
 let old_s=sums[lane];let old_l=limbs[lane];
 let mut log=NFM_WindowLog{replies,left:[[0;8];4],right:[0;4],order:[99;32],calls:0};
 for term in 8..core::cmp::min(8+4,26){
  NFM_window_term(&q,&g,slot,term,term-8,&mut sums,&mut log);
 }
 let mut expected=old_s;
 for off in 0..4{
  expected+=replies[off][lane];
  let at=slot*120+(8+off)*4;
  assert_eq!(log.left[off][lane],g[8+off].to_limbs()[lane]);
  assert_eq!(log.right[off],u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]));
  assert_eq!(log.order[off*8+lane],off*8+lane);
 }
 assert_eq!(log.calls,4*8);assert_eq!(sums[lane],expected);
 NFM_fold(sums,&mut limbs);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_window_2){(old_l+(expected&0x7fffffff)+(expected>>31))^1}else{old_l+(expected&0x7fffffff)+(expected>>31)});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn window_3(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);
 let mut limbs:[u64;8]=kani::any();let mut sums:[u64;8]=kani::any();
 let replies:[[u64;8];4]=kani::any();let lane:usize=kani::any();kani::assume(lane<8);
 for j in 0..8{kani::assume(limbs[j]<=6*10737418238u64);kani::assume(sums[j]<=0*NFM_BOUND);}
 for off in 0..4{
  let at=slot*120+(12+off)*4;
  kani::assume(u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])<2147483647);
  for j in 0..8{kani::assume(replies[off][j]<=NFM_BOUND);}
 }
 let old_s=sums[lane];let old_l=limbs[lane];
 let mut log=NFM_WindowLog{replies,left:[[0;8];4],right:[0;4],order:[99;32],calls:0};
 for term in 12..core::cmp::min(12+4,26){
  NFM_window_term(&q,&g,slot,term,term-12,&mut sums,&mut log);
 }
 let mut expected=old_s;
 for off in 0..4{
  expected+=replies[off][lane];
  let at=slot*120+(12+off)*4;
  assert_eq!(log.left[off][lane],g[12+off].to_limbs()[lane]);
  assert_eq!(log.right[off],u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]));
  assert_eq!(log.order[off*8+lane],off*8+lane);
 }
 assert_eq!(log.calls,4*8);assert_eq!(sums[lane],expected);
 NFM_fold(sums,&mut limbs);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_window_3){(old_l+(expected&0x7fffffff)+(expected>>31))^1}else{old_l+(expected&0x7fffffff)+(expected>>31)});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn window_4(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);
 let mut limbs:[u64;8]=kani::any();let mut sums:[u64;8]=kani::any();
 let replies:[[u64;8];4]=kani::any();let lane:usize=kani::any();kani::assume(lane<8);
 for j in 0..8{kani::assume(limbs[j]<=6*10737418238u64);kani::assume(sums[j]<=0*NFM_BOUND);}
 for off in 0..4{
  let at=slot*120+(16+off)*4;
  kani::assume(u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])<2147483647);
  for j in 0..8{kani::assume(replies[off][j]<=NFM_BOUND);}
 }
 let old_s=sums[lane];let old_l=limbs[lane];
 let mut log=NFM_WindowLog{replies,left:[[0;8];4],right:[0;4],order:[99;32],calls:0};
 for term in 16..core::cmp::min(16+4,26){
  NFM_window_term(&q,&g,slot,term,term-16,&mut sums,&mut log);
 }
 let mut expected=old_s;
 for off in 0..4{
  expected+=replies[off][lane];
  let at=slot*120+(16+off)*4;
  assert_eq!(log.left[off][lane],g[16+off].to_limbs()[lane]);
  assert_eq!(log.right[off],u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]));
  assert_eq!(log.order[off*8+lane],off*8+lane);
 }
 assert_eq!(log.calls,4*8);assert_eq!(sums[lane],expected);
 NFM_fold(sums,&mut limbs);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_window_4){(old_l+(expected&0x7fffffff)+(expected>>31))^1}else{old_l+(expected&0x7fffffff)+(expected>>31)});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn window_5(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);
 let mut limbs:[u64;8]=kani::any();let mut sums:[u64;8]=kani::any();
 let replies:[[u64;8];4]=kani::any();let lane:usize=kani::any();kani::assume(lane<8);
 for j in 0..8{kani::assume(limbs[j]<=6*10737418238u64);kani::assume(sums[j]<=0*NFM_BOUND);}
 for off in 0..4{
  let at=slot*120+(20+off)*4;
  kani::assume(u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])<2147483647);
  for j in 0..8{kani::assume(replies[off][j]<=NFM_BOUND);}
 }
 let old_s=sums[lane];let old_l=limbs[lane];
 let mut log=NFM_WindowLog{replies,left:[[0;8];4],right:[0;4],order:[99;32],calls:0};
 for term in 20..core::cmp::min(20+4,26){
  NFM_window_term(&q,&g,slot,term,term-20,&mut sums,&mut log);
 }
 let mut expected=old_s;
 for off in 0..4{
  expected+=replies[off][lane];
  let at=slot*120+(20+off)*4;
  assert_eq!(log.left[off][lane],g[20+off].to_limbs()[lane]);
  assert_eq!(log.right[off],u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]));
  assert_eq!(log.order[off*8+lane],off*8+lane);
 }
 assert_eq!(log.calls,4*8);assert_eq!(sums[lane],expected);
 NFM_fold(sums,&mut limbs);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_window_5){(old_l+(expected&0x7fffffff)+(expected>>31))^1}else{old_l+(expected&0x7fffffff)+(expected>>31)});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn window_6(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);
 let mut limbs:[u64;8]=kani::any();let mut sums:[u64;8]=kani::any();
 let replies:[[u64;8];4]=kani::any();let lane:usize=kani::any();kani::assume(lane<8);
 for j in 0..8{kani::assume(limbs[j]<=6*10737418238u64);kani::assume(sums[j]<=2*NFM_BOUND);}
 for off in 0..2{
  let at=slot*120+(24+off)*4;
  kani::assume(u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])<2147483647);
  for j in 0..8{kani::assume(replies[off][j]<=NFM_BOUND);}
 }
 let old_s=sums[lane];let old_l=limbs[lane];
 let mut log=NFM_WindowLog{replies,left:[[0;8];4],right:[0;4],order:[99;32],calls:0};
 for term in 24..core::cmp::min(24+4,26){
  NFM_window_term(&q,&g,slot,term,term-24,&mut sums,&mut log);
 }
 let mut expected=old_s;
 for off in 0..2{
  expected+=replies[off][lane];
  let at=slot*120+(24+off)*4;
  assert_eq!(log.left[off][lane],g[24+off].to_limbs()[lane]);
  assert_eq!(log.right[off],u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]));
  assert_eq!(log.order[off*8+lane],off*8+lane);
 }
 assert_eq!(log.calls,2*8);assert_eq!(sums[lane],expected);
 NFM_fold(sums,&mut limbs);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_window_6){(old_l+(expected&0x7fffffff)+(expected>>31))^1}else{old_l+(expected&0x7fffffff)+(expected>>31)});
}

// Expose the frozen scalar unwrap terminal as an explicit abort tag. No
// coefficient read/product/fold is executed on that terminal branch.
fn NFM_read_or_abort(q:&[u8;608],slot:usize,term:usize)->Result<M31,usize>{
 match M31::from_le_bytes(q[slot*120+term*4..slot*120+term*4+4].try_into().unwrap()){
  Some(s)=>Ok(s),None=>Err(term)
 }
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn reject_0(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && 0<=term && term<4 && lane<8);
 let mut sums:[u64;8]=kani::any();let limbs:[u64;8]=kani::any();
 let old_s=sums[lane];let old_l=limbs[lane];let mut calls=0;
 let at=slot*120+term*4;let word=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(word>=2147483647);
 let terminal=match NFM_read_or_abort(&q,slot,term){
  Err(t)=>{assert_eq!(t,term);true},
  Ok(s)=>{let c=g[term].to_limbs();calls+=1;sums[lane]=u64::from(c[lane])+u64::from(s.0);false}
 };
 assert!(terminal);assert_eq!(calls,0);assert_eq!(sums[lane],old_s);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_reject_0){old_l^1}else{old_l});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn reject_1(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && 4<=term && term<8 && lane<8);
 let mut sums:[u64;8]=kani::any();let limbs:[u64;8]=kani::any();
 let old_s=sums[lane];let old_l=limbs[lane];let mut calls=0;
 let at=slot*120+term*4;let word=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(word>=2147483647);
 let terminal=match NFM_read_or_abort(&q,slot,term){
  Err(t)=>{assert_eq!(t,term);true},
  Ok(s)=>{let c=g[term].to_limbs();calls+=1;sums[lane]=u64::from(c[lane])+u64::from(s.0);false}
 };
 assert!(terminal);assert_eq!(calls,0);assert_eq!(sums[lane],old_s);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_reject_1){old_l^1}else{old_l});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn reject_2(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && 8<=term && term<12 && lane<8);
 let mut sums:[u64;8]=kani::any();let limbs:[u64;8]=kani::any();
 let old_s=sums[lane];let old_l=limbs[lane];let mut calls=0;
 let at=slot*120+term*4;let word=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(word>=2147483647);
 let terminal=match NFM_read_or_abort(&q,slot,term){
  Err(t)=>{assert_eq!(t,term);true},
  Ok(s)=>{let c=g[term].to_limbs();calls+=1;sums[lane]=u64::from(c[lane])+u64::from(s.0);false}
 };
 assert!(terminal);assert_eq!(calls,0);assert_eq!(sums[lane],old_s);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_reject_2){old_l^1}else{old_l});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn reject_3(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && 12<=term && term<16 && lane<8);
 let mut sums:[u64;8]=kani::any();let limbs:[u64;8]=kani::any();
 let old_s=sums[lane];let old_l=limbs[lane];let mut calls=0;
 let at=slot*120+term*4;let word=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(word>=2147483647);
 let terminal=match NFM_read_or_abort(&q,slot,term){
  Err(t)=>{assert_eq!(t,term);true},
  Ok(s)=>{let c=g[term].to_limbs();calls+=1;sums[lane]=u64::from(c[lane])+u64::from(s.0);false}
 };
 assert!(terminal);assert_eq!(calls,0);assert_eq!(sums[lane],old_s);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_reject_3){old_l^1}else{old_l});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn reject_4(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && 16<=term && term<20 && lane<8);
 let mut sums:[u64;8]=kani::any();let limbs:[u64;8]=kani::any();
 let old_s=sums[lane];let old_l=limbs[lane];let mut calls=0;
 let at=slot*120+term*4;let word=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(word>=2147483647);
 let terminal=match NFM_read_or_abort(&q,slot,term){
  Err(t)=>{assert_eq!(t,term);true},
  Ok(s)=>{let c=g[term].to_limbs();calls+=1;sums[lane]=u64::from(c[lane])+u64::from(s.0);false}
 };
 assert!(terminal);assert_eq!(calls,0);assert_eq!(sums[lane],old_s);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_reject_4){old_l^1}else{old_l});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn reject_5(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && 20<=term && term<24 && lane<8);
 let mut sums:[u64;8]=kani::any();let limbs:[u64;8]=kani::any();
 let old_s=sums[lane];let old_l=limbs[lane];let mut calls=0;
 let at=slot*120+term*4;let word=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(word>=2147483647);
 let terminal=match NFM_read_or_abort(&q,slot,term){
  Err(t)=>{assert_eq!(t,term);true},
  Ok(s)=>{let c=g[term].to_limbs();calls+=1;sums[lane]=u64::from(c[lane])+u64::from(s.0);false}
 };
 assert!(terminal);assert_eq!(calls,0);assert_eq!(sums[lane],old_s);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_reject_5){old_l^1}else{old_l});
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn reject_6(){
 let q:[u8;608]=kani::any();let g:[WideExact;29]=kani::any();
 let slot:usize=kani::any();let term:usize=kani::any();let lane:usize=kani::any();
 kani::assume(slot<4 && 24<=term && term<26 && lane<8);
 let mut sums:[u64;8]=kani::any();let limbs:[u64;8]=kani::any();
 let old_s=sums[lane];let old_l=limbs[lane];let mut calls=0;
 let at=slot*120+term*4;let word=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
 kani::assume(word>=2147483647);
 let terminal=match NFM_read_or_abort(&q,slot,term){
  Err(t)=>{assert_eq!(t,term);true},
  Ok(s)=>{let c=g[term].to_limbs();calls+=1;sums[lane]=u64::from(c[lane])+u64::from(s.0);false}
 };
 assert!(terminal);assert_eq!(calls,0);assert_eq!(sums[lane],old_s);
 assert_eq!(limbs[lane],if cfg!(NFM_wrong_reject_6){old_l^1}else{old_l});
}
