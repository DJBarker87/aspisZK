// Same scalar, streamed private contractions; no 17-element gather arrays.
// Only the operands read by the retained kernel are validated/used here.
#[inline(never)]
pub(super) fn r81_sparse_scalar_after_ordinary(
    coins:&[K],workspace:&[K],kernel:&r17_weighted_groups::Kernel,
)->K {
    assert!(coins.len()>=271 && workspace.len()>=531);
    let hb=&workspace[403..531];
    let (normal,carry,_)=kernel.geometry_parts();
    let mut result=r85_private::Dot::new();
    for low in 0..16 {
        let mut normal_sum=r85_private::Dot::new();
        let mut carry_sum=r85_private::Dot::new();
        let mut i=(11*low)%16;
        while i<271 {
            let a=r85_in(coins[i]).expect("canonical sparse coin");
            let group=(128+3*i)>>4;
            normal_sum.push(a,r85_in(hb[group]).expect("canonical sparse normal operand"));
            if low<3 {
                carry_sum.push(a,r85_in(hb[64+group]).expect("canonical sparse carry operand"));
            }
            i+=16;
        }
        result.push(r85_in(normal[low]).expect("canonical sparse normal"),normal_sum.finish());
        if low<3 {
            result.push(r85_in(carry[low]).expect("canonical sparse carry"),carry_sum.finish());
        }
    }
    r85_out(result.finish().half_pow(8).expect("fixed half exponent"))
}
