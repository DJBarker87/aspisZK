mod canonical {
    pub const P:u32=0x7fff_ffff;
    #[inline(always)] pub(crate) fn reduce(mut x:u64)->u32 {
        x=(x & u64::from(P))+(x>>31u32);
        x=(x & u64::from(P))+(x>>31u32);
        if x>=u64::from(P) {(x-u64::from(P)) as u32}else{x as u32}
    }
    pub struct Q([u32;4]);
    impl Q {
        pub const fn limbs(self)->[u32;4]{self.0}
    }
    pub struct Dot { sums:[u64;4] }
    impl Dot {
        pub fn finish(self)->Q {Q(self.sums.map(reduce))}
    }
    pub fn finish_entry(sums:[u64;4])->[u32;4] {Dot{sums}.finish().limbs()}
}
pub fn reduce_entry(x:u64)->u32 {canonical::reduce(x)}
pub fn finish_entry(sums:[u64;4])->[u32;4] {canonical::finish_entry(sums)}
pub fn option_context_anchor(v:Option<u8>)->Option<u8>{v}
