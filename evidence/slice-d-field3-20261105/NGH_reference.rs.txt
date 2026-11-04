use super::*;
pub(super) fn NGH_accumulate_ref(
    mut sums: [[u64; 3]; 3],
    left: QM31,
    right: QM31,
) -> [[u64; 3]; 3] {
    let left_sum = left.c0.add(left.c1);
    let right_sum = right.c0.add(right.c1);
    let left_components = [
        [left.c0.a, left.c0.b, left.c0.a.add(left.c0.b)],
        [left.c1.a, left.c1.b, left.c1.a.add(left.c1.b)],
        [left_sum.a, left_sum.b, left_sum.a.add(left_sum.b)],
    ];
    let right_components = [
        [right.c0.a, right.c0.b, right.c0.a.add(right.c0.b)],
        [right.c1.a, right.c1.b, right.c1.a.add(right.c1.b)],
        [right_sum.a, right_sum.b, right_sum.a.add(right_sum.b)],
    ];
    for component in 0..3 {
        for channel in 0..3 {
            sums[component][channel] += left_components[component][channel].0 as u64
                * right_components[component][channel].0 as u64;
        }
    }
    sums
}

#[inline(always)]
pub(super) fn NGH_small_ref<const N: usize>(left: [QM31; N], right: [QM31; N]) -> QM31 {
    debug_assert!(N >= 2 && N <= 4);
    // [quadratic-extension component][CM31 Karatsuba channel].
    let mut sums = [[0u64; 3]; 3];
    let mut index = 0usize;
    while index < N {
        sums = NGH_accumulate_ref(sums, left[index], right[index]);
        index += 1;
    }

    qm31_from_karatsuba_channel_sums(sums)
}


pub(super) fn domain(s:[[u64;3];3],l:QM31,r:QM31)->bool{
 let canonical=|x:QM31|x.c0.a.0<P&&x.c0.b.0<P&&x.c1.a.0<P&&x.c1.b.0<P;
 canonical(l)&&canonical(r)&&s[0][0]<=3*4611686009837453316&&s[0][1]<=3*4611686009837453316&&s[0][2]<=3*4611686009837453316&&s[1][0]<=3*4611686009837453316&&s[1][1]<=3*4611686009837453316&&s[1][2]<=3*4611686009837453316&&s[2][0]<=3*4611686009837453316&&s[2][1]<=3*4611686009837453316&&s[2][2]<=3*4611686009837453316
}
#[cfg(NGH_for_diagnostic)]
#[kani::proof_for_contract(qm31_accumulate_product_channels)]
fn actual_for_contract(){qm31_accumulate_product_channels(kani::any(),QM31::ZERO,QM31::ZERO);}
