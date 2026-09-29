// Exact R84 first-pair contraction, with common tensor factors retained.
// Big-endian source points; rows 14/15/30 and balancing pivot 1023.
// No divisions, challenge exclusions, or different affine observations.
#[inline(never)]
fn r87_point_parts(z:&[K;10],use_x:bool)->(K,K,[K;2]) {
    let mut hi0=K::ONE.sub(z[0]);let mut hi1=z[0];
    for i in 1..5 {hi0=hi0.mul(K::ONE.sub(z[i]));hi1=hi1.mul(z[i]);}
    let hi0_one=hi0.mul(z[5]);let hi0_zero=hi0.sub(hi0_one);
    let pivot=hi1.mul(z[5]).mul(z[9]);
    let gaps=[hi0_zero.mul(K::ONE.sub(z[9])).sub(pivot),
        if use_x {hi0_one.mul(K::ONE.sub(z[9])).sub(pivot)}
        else{hi0_zero.mul(z[9]).sub(pivot)}];
    let ordinary=z[6].mul(z[7]).mul(z[8]);
    let xor12=K::ONE.sub(z[6]).mul(K::ONE.sub(z[7])).mul(z[8]);
    (ordinary,xor12,gaps)
}

#[inline(never)]
pub(super) fn ordinary_and_first(z:&[K;10],kappa:K,use_x:bool)->([K;2],[K;2]) {
    let t=basis_transport::transport();
    // Keep the old generic helper as the fallback for a different source map.
    // Selected-profile source inventory/export checks establish the fast case.
    if t.order[0]!=14 || t.order[1]!=15 || t.order[2]!=30 || t.order[1023]!=1023
        || ![14,15,30,1023].into_iter().all(|r|t.inactive[r]) {
        return (ordinary_pair(z,kappa,use_x),super::r18_compact_g::first_pair(z,use_x));
    }
    let points=corelib::v6_transcript::v6_statement_points(z);
    let k2=kappa.square();let k3=k2.mul(kappa);
    let (normal,xor12,gaps)=r87_point_parts(z,use_x);
    let (successor,_,successor_gaps)=r87_point_parts(&points[1],use_x);
    let scale=corelib::field::qm31_sum_products2([kappa,k3],[normal,xor12]);
    let next_scale=k2.mul(successor);
    let ordinary=core::array::from_fn(|i|
        corelib::field::qm31_sum_products2([scale,next_scale],[gaps[i],successor_gaps[i]]));
    let first=gaps.map(|g|normal.mul(g));
    (ordinary,first)
}

#[cfg(not(target_os="solana"))]
pub(super) fn r87_check(z:&[K;10],kappa:K,use_x:bool) {
    let actual=ordinary_and_first(z,kappa,use_x);
    assert_eq!(actual.0,ordinary_pair(z,kappa,use_x));
    assert_eq!(actual.1,super::r18_compact_g::first_pair(z,use_x));
    // Compare against all 1024 source rows and the actual dual transform.
    let w=super::r17_opening_weights::original_weights_reference(z,kappa,false);
    let dual=basis_transport::transport().dual(&w);
    assert_eq!(actual.0,[dual[0],dual[if use_x{2}else{1}]]);
}
