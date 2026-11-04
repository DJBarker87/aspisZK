use super::*;
const NGH_P:u64=2147483647;
fn canonical(q:QM31)->bool {q.c0.a.0<NGH_P as u32 && q.c0.b.0<NGH_P as u32 && q.c1.a.0<NGH_P as u32 && q.c1.b.0<NGH_P as u32}
#[inline(never)]
fn native_product(a:u64,b:u64)->u64 { a*b }
fn product_stub(a:u64,b:u64)->u64 {
 kani::assume(a<NGH_P && b<NGH_P);
 let reply:u64=kani::any(); kani::assume(reply==a*b);reply
}
fn bound(s:[[u64;3];3],i:usize,j:usize,l:QM31,r:QM31)->bool {canonical(l)&&canonical(r)&&s[i][j]<=3*(NGH_P-1)*(NGH_P-1)}
fn ref_00(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    sums[0][0] += native_product(left_components[0][0].0 as u64,right_components[0][0].0 as u64);
    sums
}
#[kani::requires(bound(sums,0,0,left,right))]
#[kani::ensures(|out| if cfg!(NGH_invert) {out[0][0] != ref_00(sums,left,right)[0][0]} else {out[0][0] == ref_00(sums,left,right)[0][0]})]
fn cell_00(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    let component=0; let channel=0;
    sums[component][channel] += native_product(left_components[component][channel].0 as u64,right_components[component][channel].0 as u64);
    sums
}
#[kani::proof_for_contract(cell_00)]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn proof_00() {let sums=kani::any();let left=kani::any();let right=kani::any();cell_00(sums,left,right);}
fn ref_01(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    sums[0][1] += native_product(left_components[0][1].0 as u64,right_components[0][1].0 as u64);
    sums
}
#[kani::requires(bound(sums,0,1,left,right))]
#[kani::ensures(|out| if cfg!(NGH_invert) {out[0][1] != ref_01(sums,left,right)[0][1]} else {out[0][1] == ref_01(sums,left,right)[0][1]})]
fn cell_01(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    let component=0; let channel=1;
    sums[component][channel] += native_product(left_components[component][channel].0 as u64,right_components[component][channel].0 as u64);
    sums
}
#[kani::proof_for_contract(cell_01)]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn proof_01() {let sums=kani::any();let left=kani::any();let right=kani::any();cell_01(sums,left,right);}
fn ref_02(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    sums[0][2] += native_product(left_components[0][2].0 as u64,right_components[0][2].0 as u64);
    sums
}
#[kani::requires(bound(sums,0,2,left,right))]
#[kani::ensures(|out| if cfg!(NGH_invert) {out[0][2] != ref_02(sums,left,right)[0][2]} else {out[0][2] == ref_02(sums,left,right)[0][2]})]
fn cell_02(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    let component=0; let channel=2;
    sums[component][channel] += native_product(left_components[component][channel].0 as u64,right_components[component][channel].0 as u64);
    sums
}
#[kani::proof_for_contract(cell_02)]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn proof_02() {let sums=kani::any();let left=kani::any();let right=kani::any();cell_02(sums,left,right);}
fn ref_10(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    sums[1][0] += native_product(left_components[1][0].0 as u64,right_components[1][0].0 as u64);
    sums
}
#[kani::requires(bound(sums,1,0,left,right))]
#[kani::ensures(|out| if cfg!(NGH_invert) {out[1][0] != ref_10(sums,left,right)[1][0]} else {out[1][0] == ref_10(sums,left,right)[1][0]})]
fn cell_10(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    let component=1; let channel=0;
    sums[component][channel] += native_product(left_components[component][channel].0 as u64,right_components[component][channel].0 as u64);
    sums
}
#[kani::proof_for_contract(cell_10)]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn proof_10() {let sums=kani::any();let left=kani::any();let right=kani::any();cell_10(sums,left,right);}
fn ref_11(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    sums[1][1] += native_product(left_components[1][1].0 as u64,right_components[1][1].0 as u64);
    sums
}
#[kani::requires(bound(sums,1,1,left,right))]
#[kani::ensures(|out| if cfg!(NGH_invert) {out[1][1] != ref_11(sums,left,right)[1][1]} else {out[1][1] == ref_11(sums,left,right)[1][1]})]
fn cell_11(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    let component=1; let channel=1;
    sums[component][channel] += native_product(left_components[component][channel].0 as u64,right_components[component][channel].0 as u64);
    sums
}
#[kani::proof_for_contract(cell_11)]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn proof_11() {let sums=kani::any();let left=kani::any();let right=kani::any();cell_11(sums,left,right);}
fn ref_12(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    sums[1][2] += native_product(left_components[1][2].0 as u64,right_components[1][2].0 as u64);
    sums
}
#[kani::requires(bound(sums,1,2,left,right))]
#[kani::ensures(|out| if cfg!(NGH_invert) {out[1][2] != ref_12(sums,left,right)[1][2]} else {out[1][2] == ref_12(sums,left,right)[1][2]})]
fn cell_12(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    let component=1; let channel=2;
    sums[component][channel] += native_product(left_components[component][channel].0 as u64,right_components[component][channel].0 as u64);
    sums
}
#[kani::proof_for_contract(cell_12)]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn proof_12() {let sums=kani::any();let left=kani::any();let right=kani::any();cell_12(sums,left,right);}
fn ref_20(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    sums[2][0] += native_product(left_components[2][0].0 as u64,right_components[2][0].0 as u64);
    sums
}
#[kani::requires(bound(sums,2,0,left,right))]
#[kani::ensures(|out| if cfg!(NGH_invert) {out[2][0] != ref_20(sums,left,right)[2][0]} else {out[2][0] == ref_20(sums,left,right)[2][0]})]
fn cell_20(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    let component=2; let channel=0;
    sums[component][channel] += native_product(left_components[component][channel].0 as u64,right_components[component][channel].0 as u64);
    sums
}
#[kani::proof_for_contract(cell_20)]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn proof_20() {let sums=kani::any();let left=kani::any();let right=kani::any();cell_20(sums,left,right);}
fn ref_21(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    sums[2][1] += native_product(left_components[2][1].0 as u64,right_components[2][1].0 as u64);
    sums
}
#[kani::requires(bound(sums,2,1,left,right))]
#[kani::ensures(|out| if cfg!(NGH_invert) {out[2][1] != ref_21(sums,left,right)[2][1]} else {out[2][1] == ref_21(sums,left,right)[2][1]})]
fn cell_21(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    let component=2; let channel=1;
    sums[component][channel] += native_product(left_components[component][channel].0 as u64,right_components[component][channel].0 as u64);
    sums
}
#[kani::proof_for_contract(cell_21)]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn proof_21() {let sums=kani::any();let left=kani::any();let right=kani::any();cell_21(sums,left,right);}
fn ref_22(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    sums[2][2] += native_product(left_components[2][2].0 as u64,right_components[2][2].0 as u64);
    sums
}
#[kani::requires(bound(sums,2,2,left,right))]
#[kani::ensures(|out| if cfg!(NGH_invert) {out[2][2] != ref_22(sums,left,right)[2][2]} else {out[2][2] == ref_22(sums,left,right)[2][2]})]
fn cell_22(mut sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3] {
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
    let component=2; let channel=2;
    sums[component][channel] += native_product(left_components[component][channel].0 as u64,right_components[component][channel].0 as u64);
    sums
}
#[kani::proof_for_contract(cell_22)]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn proof_22() {let sums=kani::any();let left=kani::any();let right=kani::any();cell_22(sums,left,right);}
#[kani::proof]
#[kani::stub(native_product,product_stub)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn frame() {
 let sums:[[u64;3];3]=kani::any();let left:QM31=kani::any();let right:QM31=kani::any();
 kani::assume(bound(sums,0,0,left,right));let out=cell_00(sums,left,right);
 let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3&&(i!=0||j!=0));
 assert!(if cfg!(NGH_invert) {out[i][j]!=sums[i][j]} else {out[i][j]==sums[i][j]});
}
