//! Sparse right contraction for the selected seven-mask layout.
//! The public group array is checked before selecting this path. No prover
//! input, witness sparsity, or removed residual is used.
use super::*;
pub(super) const MASKS:[u16;7]=[59391,59390,61438,63487,63486,39321,63786];
pub(super) const GROUPS:[usize;64]=[0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,2,3,1,4,3,1,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,2,5,5,5,5,5,5,6];
pub(super) fn sparse_right(sums:&[(K,K)],carry:&[K;16],h:&[K;16])->[K;4]{
    let all=h[0].add(h[1]).add(h[2]).add(h[3]).add(h[4]).add(h[5]).add(h[6]).add(h[7]).add(h[8]).add(h[9]).add(h[10]).add(h[11]).add(h[12]).add(h[13]).add(h[14]).add(h[15]);
    let common=carry[1].add(carry[2]);
    let mut out=[sums[1].0.add(common).mul(all);4];
    out[0]=out[0].add(sums[0].0.sub(sums[1].0).mul(h[0].add(h[1])));
    out[1]=out[1].add(sums[0].0.sub(sums[1].0).mul(h[9]));
    out[1]=out[1].add(sums[2].0.sub(sums[1].0).mul(h[10]));
    out[1]=out[1].add(sums[3].0.sub(sums[1].0).mul(h[11].add(h[14])));
    out[1]=out[1].add(sums[4].0.sub(sums[1].0).mul(h[13]));
    out[2]=out[2].add(sums[4].0.sub(sums[1].0).mul(h[0]));
    out[3]=out[3].add(sums[2].0.sub(sums[1].0).mul(h[5].add(h[8])));
    out[3]=out[3].add(sums[5].0.sub(sums[1].0).mul(h[9].add(h[10]).add(h[11]).add(h[12]).add(h[13]).add(h[14])));
    out[3]=out[3].add(sums[6].0.sub(sums[1].0).mul(h[15]));
    let delta=[carry[0],carry[0].sub(common),carry[2].neg()];
    out[0]=out[0].add(delta[0].mul(h[0].add(h[1].half()).add(h[3].half().half()).add(h[7].half().half().half()).add(h[15].half().half().half().half())));
    out[1]=out[1].add(delta[0].mul(h[8].add(h[10]).add(h[13].half()).add(h[15].half().half().half().half().half().add(h[15].half()))));
    out[3]=out[3].add(delta[0].mul(h[15].half().half().half().half().half().half()));
    out[3]=out[3].add(delta[1].mul(h[8].add(h[9].half()).add(h[10]).add(h[11].half().half().add(h[11].half())).add(h[12]).add(h[13]).add(h[15].half().half().add(h[15].half()))));
    out[3]=out[3].add(delta[2].mul(h[14]));
    out[3]=out[3].sub(common.mul(h[15].half().half().half().half().half().half()));
    out
}
