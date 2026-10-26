#![allow(dead_code,non_snake_case)]
// Exact source items. Only surrounding imports/derives and cfg(kani) proofs are local.
type Rank=[u32;8];
const P:u32=0x7fff_ffff;
const QUERY_COUNT:usize=22;
const QUERY_BOUND:u32=1<<18;
const QUERY_MAX_DRAWS:usize=64;
const MAX_BATCH:usize=16;
const LEAF_BITS:u32=18;
fn block_rank(block: &[u8; 32]) -> Rank {
    core::array::from_fn(|i| {
        let j = 4 * i;
        u32::from_le_bytes([block[j], block[j + 1], block[j + 2], block[j + 3]])
    })
}
fn query_words(block: &[u8; 32]) -> [u32; 8] {
    block_rank(block).map(|word| word & (QUERY_BOUND - 1))
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum QuerySampleError {
    /// Masking is exact only when the domain size is a nonzero power of two.
    BoundNotPowerOfTwo { bound: u32 },
    /// A without-replacement sample cannot contain more points than its domain.
    CountExceedsBound { count: usize, bound: u32 },
    /// The configured candidate-draw cap was reached before `count` distinct
    /// positions were accepted. This is an explicit completeness abort.
    DrawLimitExhausted { accepted: usize, max_draws: usize },
}
#[derive(Default)]
struct QueryScan {
    accepted: [u32; QUERY_COUNT],
    accepted_len: usize,
    draws: usize,
}
impl QueryScan {
    /// Checks before each word, with no check after the last word. In
    /// particular, success on word 8 is detected in the next block.
    fn scan(&mut self, block: &[u8; 32]) -> bool {
        for candidate in query_words(block) {
            if self.accepted_len == QUERY_COUNT || self.draws == QUERY_MAX_DRAWS {
                return true;
            }
            self.draws += 1;
            if !self.accepted[..self.accepted_len].contains(&candidate) {
                self.accepted[self.accepted_len] = candidate;
                self.accepted_len += 1;
            }
        }
        false
    }

    fn finish(self) -> Result<[u32; QUERY_COUNT], QuerySampleError> {
        if self.accepted_len == QUERY_COUNT {
            Ok(self.accepted)
        } else {
            Err(QuerySampleError::DrawLimitExhausted {
                accepted: self.accepted_len,
                max_draws: QUERY_MAX_DRAWS,
            })
        }
    }
}
pub fn queries_from_pairs(
    blocks: &[[u8; 32]; 8],
    advances: &[[u8; 32]; 8],
) -> Result<([u32; QUERY_COUNT], [u8; 32]), QuerySampleError> {
    let mut scan = QueryScan::default();
    let mut state = advances[7];
    for k in 0..8 {
        if scan.scan(&blocks[k]) {
            state = advances[k];
            break;
        }
    }
    Ok((scan.finish()?, state))
}
#[derive(Clone,Copy)]
pub enum Arity {
    Two,
    Eight,
}
impl Arity {
    #[inline(always)]
    pub const fn bits(self) -> u32 {
        match self {
            Self::Two => 1,
            Self::Eight => 3,
        }
    }
    #[inline(always)]
    pub const fn width(self) -> usize {
        1 << self.bits()
    }
    #[inline(always)]
    pub const fn levels(self) -> u32 {
        LEAF_BITS / self.bits()
    }
}
fn well_formed(indices: &[u32]) -> bool {
    !indices.is_empty()
        && indices.len() <= MAX_BATCH
        && indices.windows(2).all(|w| w[0] < w[1])
        && indices.iter().all(|&i| i < 1 << LEAF_BITS)
}
fn index_at(indices: &[u32; MAX_BATCH], index: usize) -> u32 {
    indices[index]
}
pub fn node_count(arity: Arity, indices: &[u32]) -> Option<usize> {
    if !well_formed(indices) {
        return None;
    }
    let mut level = [0u32; MAX_BATCH];
    level[..indices.len()].copy_from_slice(indices);
    let mut n = indices.len();
    let mut count = 0;
    for _ in 0..arity.levels() {
        let mut w = 0;
        let mut i = 0;
        while i < n {
            let parent = index_at(&level, i) >> arity.bits();
            let mut j = i;
            while j < n && index_at(&level, j) >> arity.bits() == parent {
                j += 1;
            }
            count += arity.width() - (j - i);
            level[w] = parent;
            w += 1;
            i = j;
        }
        n = w;
    }
    Some(count)
}
fn qm31_div_pass(mut rank: [u32; 8]) -> ([u32; 8], u32) {
    let mut remainder = 0u64;
    let mut j = 8usize;
    while j > 0 {
        j -= 1;
        let dividend = (remainder << 32) | u64::from(rank[j]);
        rank[j] = (dividend / u64::from(P)) as u32;
        remainder = dividend % u64::from(P);
    }
    (rank, remainder as u32)
}
fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
    for digit in digits {
        let sum = u64::from(*digit) + u64::from(addend);
        *digit = (sum % u64::from(P)) as u32;
        addend = (sum / u64::from(P)) as u32;
    }
    debug_assert!(addend <= 1);
    addend != 0
}
#[cfg(kani)]
mod PV_L2_proofs {
use super::*;
fn arbitrary_scan(len:usize,draws:usize)->QueryScan {
 QueryScan {accepted:kani::any(),accepted_len:len,draws}
}
fn equal_prefix(a:&QueryScan,b:&QueryScan) {
 assert_eq!(a.accepted_len,b.accepted_len); assert_eq!(a.draws,b.draws);
 for i in 0..22 {if i<a.accepted_len {assert_eq!(a.accepted[i],b.accepted[i]);}}
}
#[kani::proof] #[kani::unwind(34)]
fn F5_stop_count() {
 let mut a=arbitrary_scan(22,kani::any());kani::assume(a.draws<=64);
 let mut b=QueryScan{accepted:a.accepted,accepted_len:22,draws:a.draws};
 let x:[u8;32]=kani::any();let y:[u8;32]=kani::any();
 assert!(a.scan(&x));assert!(b.scan(&y));equal_prefix(&a,&b);
}
#[kani::proof] #[kani::unwind(34)]
fn F5_stop_draws() {
 let len:usize=kani::any();kani::assume(len<=22);
 let mut a=arbitrary_scan(len,64);let mut b=QueryScan{accepted:a.accepted,accepted_len:len,draws:64};
 assert!(a.scan(&kani::any()));assert!(b.scan(&kani::any()));equal_prefix(&a,&b);
}
#[kani::proof] #[kani::unwind(34)]
fn F5_query_words() {
 let x:[u8;32]=kani::any();let w=query_words(&x);
 for i in 0..8 {assert!(w[i]<QUERY_BOUND);assert_eq!(w[i],u32::from_le_bytes([x[4*i],x[4*i+1],x[4*i+2],x[4*i+3]]) & (QUERY_BOUND-1));}
}
#[kani::proof] #[kani::unwind(34)]
fn F5_scan_unused_suffix() {
 let len:usize=kani::any();kani::assume(len<=22);let draws:usize=kani::any();kani::assume(draws<=64);
 let mut a=arbitrary_scan(len,draws);let mut b=arbitrary_scan(len,draws);
 for i in 0..22 {if i<len {b.accepted[i]=a.accepted[i];}}
 let block:[u8;32]=kani::any();assert_eq!(a.scan(&block),b.scan(&block));equal_prefix(&a,&b);
}
#[kani::proof] #[kani::unwind(34)]
fn F5_finish_success() {
 let a=arbitrary_scan(22,kani::any());let accepted=a.accepted; assert_eq!(a.finish(),Ok(accepted));
}
#[kani::proof] #[kani::unwind(34)]
fn F5_finish_failure() {
 let len:usize=kani::any();kani::assume(len<22);let a=arbitrary_scan(len,kani::any());
 assert_eq!(a.finish(),Err(QuerySampleError::DrawLimitExhausted{accepted:len,max_draws:64}));
}
#[kani::proof] #[kani::unwind(34)]
fn F5_pairs_failure_advances() {
 let block:[u8;32]=[0;32];let blocks=[block;8];let advances:[[u8;32];8]=kani::any();
 assert_eq!(queries_from_pairs(&blocks,&advances),Err(QuerySampleError::DrawLimitExhausted{accepted:1,max_draws:64}));
}
#[kani::proof] #[kani::unwind(34)]
fn F5_gamma_add() {
 let digits:[u32;8]=kani::any();let add:u32=kani::any();kani::assume(add<=257);
 for i in 0..8 {kani::assume(digits[i]<P);}
 let mut a=digits;let mut b=digits;let ca=add_small_base_p(&mut a,add);let cb=add_small_base_p(&mut b,add);
 assert_eq!(ca,cb); for i in 0..8 {assert_eq!(a[i],b[i]);assert!(a[i]<P);}
}
#[kani::proof] #[kani::unwind(34)]
fn F5_div_pass() {
 let rank:[u32;8]=kani::any();let (a,r)=qm31_div_pass(rank);let (b,s)=qm31_div_pass(rank);
 assert!(r<P);assert_eq!(r,s);for i in 0..8 {assert_eq!(a[i],b[i]);}
}
#[kani::proof] #[kani::unwind(34)]
fn F6_well_formed() {
 let xs:[u32;16]=kani::any();let n:usize=kani::any();kani::assume(n<=16);
 let a=well_formed(&xs[..n]);let b=well_formed(&xs[..n]);assert_eq!(a,b);
 if a {assert!(n>0);for i in 0..16 {if i<n {assert!(xs[i]<1<<18);}if i+1<n {assert!(xs[i]<xs[i+1]);}}}
}
#[kani::proof] #[kani::unwind(34)]
fn F6_single_binary() {let x:u32=kani::any();kani::assume(x<1<<18);assert_eq!(node_count(Arity::Two,&[x]),Some(18));}
#[kani::proof] #[kani::unwind(34)]
fn F6_single_eight() {let x:u32=kani::any();kani::assume(x<1<<18);assert_eq!(node_count(Arity::Eight,&[x]),Some(42));}
#[kani::proof] #[kani::unwind(34)]
fn F6_pair_binary() {
 let x:u32=kani::any();kani::assume(x<1<<17);assert_eq!(node_count(Arity::Two,&[2*x,2*x+1]),Some(17));
}
#[kani::proof] #[kani::unwind(34)]
fn F6_arbitrary_binary() {let xs:[u32;16]=kani::any();let n:usize=kani::any();kani::assume(n<=16);let a=node_count(Arity::Two,&xs[..n]);let b=node_count(Arity::Two,&xs[..n]);assert_eq!(a,b);}
#[kani::proof] #[kani::unwind(34)]
fn F6_bad_empty() {assert_eq!(node_count(Arity::Two,&[]),None);assert_eq!(node_count(Arity::Eight,&[]),None);}
#[kani::proof] #[kani::unwind(34)]
fn F6_bad_range() {let x:u32=kani::any();kani::assume(x>=1<<18);assert_eq!(node_count(Arity::Two,&[x]),None);assert_eq!(node_count(Arity::Eight,&[x]),None);}
#[kani::proof] #[kani::unwind(34)]
fn F6_bad_order() {let x:u32=kani::any();let y:u32=kani::any();kani::assume(x>=y);assert_eq!(node_count(Arity::Two,&[x,y]),None);}
#[kani::proof] #[kani::unwind(34)]
fn F5_gamma_zero() {let mut x=[0;8];assert!(!add_small_base_p(&mut x,0));for i in 0..8 {assert_eq!(x[i],0);}}
#[kani::proof] #[kani::unwind(34)]
fn F5_gamma_wrap() {let mut x=[P-1;8];assert!(add_small_base_p(&mut x,1));for i in 0..8 {assert_eq!(x[i],0);}}
#[kani::proof] #[kani::unwind(34)]
fn F5_div_zero() {let (q,r)=qm31_div_pass([0;8]);assert_eq!(r,0);for i in 0..8 {assert_eq!(q[i],0);}}
}
