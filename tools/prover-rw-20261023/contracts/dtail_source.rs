use aspis_core::field::{QM31,M31};
fn add_d_tail(mask_sum:QM31,dc:&[QM31;1024])->QM31 {
    let first=d_tail_side(dc,0).mul_m31(M31(512));
    let mask_sum=mask_sum.add(first);
    let second=d_tail_side(dc,28).mul_m31(M31(512));
    mask_sum.add(second)
}

fn d_tail_side(dc:&[QM31;1024],offset:usize)->QM31 {
    // Preserve the shipped h0 term in addition to the j=0 summand.
    d_tail_sum(dc,offset,0,dc[offset])
}

fn d_tail_sum(dc:&[QM31;1024],offset:usize,j:usize,sum:QM31)->QM31 {
    if j==28 {return sum;}
    let next=sum.add(dc[offset+j]);
    d_tail_sum(dc,offset,j+1,next)
}
pub(crate) fn actual(mask_sum:QM31,dc:&[QM31;1024])->QM31 {add_d_tail(mask_sum,dc)}
pub(crate) fn expected(mut mask_sum:QM31,dc:&[QM31;1024])->QM31 {
        for side in 0..2 {
            let h = &dc[28*side..28*(side+1)];
            mask_sum = mask_sum.add(h.iter().copied().fold(h[0], QM31::add).mul_m31(M31(512)));
        }
mask_sum
}
