// Private canonical operands; bounded raw representatives, canonical result.
// At most 4096 partial folds, each <2^34, sum <2^46. No u64 wrap.
pub struct Dot { sums:[u64;4], count:usize }
impl Dot {
    pub fn new()->Self {Self{sums:[0;4],count:0}}
    #[inline(always)]
    pub fn push(&mut self,a:Q,b:Q) {
        assert!(self.count<4096);self.count+=1;
        let raw=a.raw(b);
        for j in 0..4 {
            self.sums[j]=self.sums[j].wrapping_add(
                (raw[j]&u64::from(P)).wrapping_add(raw[j]>>31));
        }
    }
    pub fn finish(self)->Q {Q(self.sums.map(reduce))}
}
