//! Research draft, NOT compiled/source-integrated here. New transcript profile.
//! Absorb BOTH sent coefficients before deriving beta. Preserve the incoming
//! claim's TWO original interpolant subtractions. No extra subtraction afterward.
use super::corelib::field::{QM31 as K, qm31_sum_products4};
pub fn coefficients(claim:K,sent:[K;2])->[K;3] {
    [sent[0],claim.sub(sent[0].add(sent[0])).sub(sent[1]),sent[1]]
}
pub fn evaluate(claim:K,sent:[K;2],beta:K)->K {
    let p=coefficients(claim,sent);p[0].add(beta.mul(p[1].add(beta.mul(p[2]))))
}
/// Prover/reference helper only. Buffer-free for a multiple-of-four domain.
pub fn prover_message(qr:&[K],qg:&[K],wr:&[K],wg:&[K])->Option<[K;2]> {
    let n=qr.len();
    if n==0||n%4!=0||qg.len()!=n||wr.len()!=n||wg.len()!=n{return None;}
    let mut p0=K::ZERO;let mut p2=K::ZERO;
    for start in (0..n).step_by(4) {
        let r=core::array::from_fn(|i|qr[start+i]);
        let w=core::array::from_fn(|i|wr[start+i]);
        let dq=core::array::from_fn(|i|qg[start+i].sub(qr[start+i]));
        let dw=core::array::from_fn(|i|wg[start+i].sub(wr[start+i]));
        p0=p0.add(qm31_sum_products4(r,w));p2=p2.add(qm31_sum_products4(dq,dw));
    }
    Some([p0,p2])
}
#[inline] pub fn lerp(r:K,g:K,beta:K)->K{r.add(beta.mul(g.sub(r)))}
/// All original packed canonical checks and authentication remain mandatory.
#[inline] pub fn combined_raw(all:K,g:K,beta:K)->K{lerp(all.sub(g),g,beta)}
pub fn interpolant(ir:[K;2],ig:[K;2],beta:K)->[K;2]{
    [lerp(ir[0],ig[0],beta),lerp(ir[1],ig[1],beta)]
}
/// Post-channel-fold weights, NOT a replacement for the original claim.
/// Never divide by beta, 1-beta, or the resulting image coefficients.
pub fn functional_scales(k:K,tau:K,beta:K)->([K;3],K,[K;2]){
    let k2=k.square();let t2=tau.square();
    ([K::ONE.sub(beta).mul(k),k2,k2.mul(k)],beta.mul(k),
     [lerp(tau,t2.mul(tau),beta),lerp(t2,t2.square(),beta)])
}
