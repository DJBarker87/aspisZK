// Included inside quotient_fold, using its existing private canonical type.
pub(super) struct Weighted {iv:[CQ;2]}
impl Weighted {
    pub(super) fn new(iv:[K;2])->Option<Self> {Some(Self{iv:[r85_in(iv[0])?,r85_in(iv[1])?]})}
    #[inline(never)]
    pub(super) fn fold(&self,all:[K;4],weights:[K;4],h:M31,use_x:bool)->Option<K> {
        let delta=self.iv[1].mul_m31(h.0)?;
        let mut values=[CQ::ZERO;4];let mut canonical_weights=[CQ::ZERO;4];
        for slot in 0..4 {
            let same=if use_x {slot<2}else{slot==0||slot==3};
            let iv=self.iv[0].add(if same{delta}else{delta.neg()});
            values[slot]=r85_in(all[slot])?.sub(iv);
            canonical_weights[slot]=r85_in(weights[slot])?;
        }
        Some(r85_out(CQ::dot(values,canonical_weights)))
    }
}
