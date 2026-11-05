struct SumLog{count:usize,owner:*const Selectors,length:usize,start:usize,end:usize,reply:QM31}
fn sum_cut(s:&Selectors,ranges:&[core::ops::Range<usize>],log:&mut SumLog)->QM31{log.count+=1;log.owner=s as *const _;log.length=ranges.len();if !ranges.is_empty(){log.start=ranges[0].start;log.end=ranges[0].end;}log.reply}
include!("NHU_poseidon_selectors_body.rs");
#[kani::proof]#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_poseidon_selectors(){let s=Selectors{high:core::array::from_fn(|_|canonical_q()),low:core::array::from_fn(|_|canonical_q())};let reply=canonical_q();let mut log=SumLog{count:0,owner:core::ptr::null(),length:0,start:0,end:0,reply};let out=NHU_poseidon_selectors_cut(&s,&mut log);let limb:usize=kani::any();kani::assume(limb<4);let i:usize=kani::any();kani::assume(i<16);assert_eq!(words(out.local[i])[limb],words(s.low[i])[limb]^if cfg!(NHU_invert){1}else{0});assert_eq!(out.block,reply);assert_eq!(log.count,1);assert_eq!(log.owner,&s as *const _);assert_eq!(log.length,1);assert_eq!(log.start,0);assert_eq!(log.end,57);}
