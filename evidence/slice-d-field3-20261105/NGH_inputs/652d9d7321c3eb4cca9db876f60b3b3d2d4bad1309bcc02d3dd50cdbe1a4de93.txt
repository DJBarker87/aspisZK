include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
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
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn actual_for_contract(){
 let q=||QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}};
 qm31_accumulate_product_channels(kani::any(),q(),q());}

pub(super) fn array_domain<const N:usize>(xs:[QM31;N])->bool{xs.iter().all(|x|x.c0.a.0<P&&x.c0.b.0<P&&x.c1.a.0<P&&x.c1.b.0<P)}
#[cfg(NGH_for_diagnostic)]
#[kani::proof_for_contract(qm31_sum_products_small)]
fn actual_small_contract(){let q=||QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}};qm31_sum_products_small([q(),q()],[q(),q()]);}

pub(super) fn native_product(a:u64,b:u64)->u64{a*b}
pub(super) fn product_stub(a:u64,b:u64)->u64{assert!(a<P as u64&&b<P as u64);let p:u64=kani::any();kani::assume(p==a*b&&p<=4611686009837453316);p}
fn one(now:u64,old:u64,a:M31,b:M31,done:bool)->bool{now==old+if done{native_product(a.0 as u64,b.0 as u64)}else{0}}
pub(super) fn progress(s:[[u64;3];3],old:[[u64;3];3],l:[[M31;3];3],r:[[M31;3];3],row:usize,col:usize)->bool{
 one(s[0][0],old[0][0],l[0][0],r[0][0],0<row||0==row&&0<col) &&
 one(s[0][1],old[0][1],l[0][1],r[0][1],0<row||0==row&&1<col) &&
 one(s[0][2],old[0][2],l[0][2],r[0][2],0<row||0==row&&2<col) &&
 one(s[1][0],old[1][0],l[1][0],r[1][0],1<row||1==row&&0<col) &&
 one(s[1][1],old[1][1],l[1][1],r[1][1],1<row||1==row&&1<col) &&
 one(s[1][2],old[1][2],l[1][2],r[1][2],1<row||1==row&&2<col) &&
 one(s[2][0],old[2][0],l[2][0],r[2][0],2<row||2==row&&0<col) &&
 one(s[2][1],old[2][1],l[2][1],r[2][1],2<row||2==row&&1<col) &&
 one(s[2][2],old[2][2],l[2][2],r[2][2],2<row||2==row&&2<col)
}
pub(super) fn row_progress(s:[[u64;3];3],old:[[u64;3];3],l:[[M31;3];3],r:[[M31;3];3],row:usize,col:usize)->bool{
 one(s[0][0],old[0][0],l[0][0],r[0][0],0==row&&0<col) &&
 one(s[0][1],old[0][1],l[0][1],r[0][1],0==row&&1<col) &&
 one(s[0][2],old[0][2],l[0][2],r[0][2],0==row&&2<col) &&
 one(s[1][0],old[1][0],l[1][0],r[1][0],1==row&&0<col) &&
 one(s[1][1],old[1][1],l[1][1],r[1][1],1==row&&1<col) &&
 one(s[1][2],old[1][2],l[1][2],r[1][2],1==row&&2<col) &&
 one(s[2][0],old[2][0],l[2][0],r[2][0],2==row&&0<col) &&
 one(s[2][1],old[2][1],l[2][1],r[2][1],2==row&&1<col) &&
 one(s[2][2],old[2][2],l[2][2],r[2][2],2==row&&2<col)
}
