// Included only by the task-copy field overlay under v8_query_affine.
// The four constant limbs are bounded raw C1 sums, not canonical M31 values.
// Caller contract: each <=7*(5*P+3). Three canonical products plus four such
// limbs fit u64; QueryAffine.lean proves every literal offset/prefix.
#[inline(always)]
pub fn research_qm31_add_raw_sum_products3_prepared(
    constant:[u64;4],left:&[PreparedQm31Multiplier;3],right:&[QM31;3]
)->QM31 {
    #[cfg(not(v8_query_affine_seeded))]
    let mut sums=[[0u64;3];3];
    #[cfg(v8_query_affine_seeded)]
    let mut sums={
        let [a,b,c,d]=constant;
        let ac=a.wrapping_add(c);
        [[a,0,a.wrapping_add(b)],[0;3],[ac,0,ac.wrapping_add(b.wrapping_add(d))]]
    };
    for index in 0..3 {
        let rhs=right[index];let sum=rhs.c0.add(rhs.c1);
        let parts=[
            [rhs.c0.a,rhs.c0.b,rhs.c0.a.add(rhs.c0.b)],
            [rhs.c1.a,rhs.c1.b,rhs.c1.a.add(rhs.c1.b)],
            [sum.a,sum.b,sum.a.add(sum.b)]];
        for i in 0..3 {for j in 0..3 {
            sums[i][j]=sums[i][j].wrapping_add(
                u64::from(left[index].components[i][j].0).wrapping_mul(u64::from(parts[i][j].0)));
        }}
    }
    #[cfg(not(v8_query_affine_seeded))]
    {
        let [a,b,c,d]=constant;
        sums[0][0]=sums[0][0].wrapping_add(a);
        sums[0][2]=sums[0][2].wrapping_add(a.wrapping_add(b));
        sums[2][0]=sums[2][0].wrapping_add(a.wrapping_add(c));
        sums[2][2]=sums[2][2].wrapping_add(a.wrapping_add(c).wrapping_add(b.wrapping_add(d)));
    }
    qm31_from_karatsuba_channel_sums(sums)
}
