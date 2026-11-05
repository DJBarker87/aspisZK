use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[path="NIH_NDE_reference.rs"] mod reference;
fn NIH_matrix_window(input:[QM31;4],output:usize,limb:usize,mut table:[[u64;4];4])->[[u64;4];4]{
 let input=input.map(extension_limbs);
 let value={
            let a = u64::from(input[0][limb]);
            let b = u64::from(input[1][limb]);
            let c = u64::from(input[2][limb]);
            let d = u64::from(input[3][limb]);
            match output {
                0 => 2 * a + 3 * b + c + d,
                1 => a + 2 * b + 3 * c + d,
                2 => a + b + 2 * c + 3 * d,
                3 => 3 * a + b + c + 2 * d,
                _ => unreachable!(),
            }
 };
 table[output][limb]=value;table
}
fn NIH_scan_step(local:[[u64;4];4],mut all_local_limbs_bounded:bool,mut output:usize,mut limb:usize)->(bool,usize,usize,bool){
 if limb<4{
            all_local_limbs_bounded &= local[output][limb] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            limb += 1;
 (all_local_limbs_bounded,output,limb,false)
 }else{output+=1;(all_local_limbs_bounded,output,limb,true)}
}
fn NIH_packed_suffix(local:[[u64;4];4])->[u64;4]{
    let bound = EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
    let packed = [
        local[0][0] + 5 * bound - local[1][1] + 2 * local[2][2]
            - local[2][3]
            - local[3][2]
            - 2 * local[3][3],
        local[0][1] + local[1][0] + local[2][2] + 2 * local[2][3] + 2 * local[3][2] + bound
            - local[3][3],
        local[0][2] + 2 * bound - local[1][3] + local[2][0] - local[3][1],
        local[0][3] + local[1][2] + local[2][1] + local[3][0],
    ];
    debug_assert!(packed[0] < 8 * bound);
    debug_assert!(packed[1] < 8 * bound);
    debug_assert!(packed[2] < 4 * bound);
    debug_assert!(packed[3] < 4 * bound);
    packed
}
fn NIH_input()->[QM31;4]{let raw:[[u32;4];4]=kani::any();
 kani::assume(raw[0][0]<2147483647&&raw[0][1]<2147483647&&raw[0][2]<2147483647&&raw[0][3]<2147483647&&raw[1][0]<2147483647&&raw[1][1]<2147483647&&raw[1][2]<2147483647&&raw[1][3]<2147483647&&raw[2][0]<2147483647&&raw[2][1]<2147483647&&raw[2][2]<2147483647&&raw[2][3]<2147483647&&raw[3][0]<2147483647&&raw[3][1]<2147483647&&raw[3][2]<2147483647&&raw[3][3]<2147483647);
 raw.map(|x|QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}})}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NDE_matrix_cell(){
 let input=NIH_input();let before:[[u64;4];4]=kani::any();let row:usize=kani::any();let limb:usize=kani::any();kani::assume(row<4&&limb<4);
 let field=|q:QM31|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0][limb];
 let expected=reference::matrix_cell_ref(field(input[0]),field(input[1]),field(input[2]),field(input[3]),row);
 let after=NIH_matrix_window(input,row,limb,before);
 let r:usize=kani::any();let j:usize=kani::any();kani::assume(r<4&&j<4);
 assert_eq!(after[r][j],if r==row&&j==limb{expected ^ if cfg!(NIH_invert){1}else{0}}else{before[r][j]});
}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NDE_scan_cell(){
 let table:[[u64;4];4]=kani::any();let flag:bool=kani::any();let row:usize=kani::any();let limb:usize=kani::any();kani::assume(row<4&&limb<=4);
 let cell=if limb<4{table[row][limb]}else{0};let expected=reference::scan_step_ref(flag,cell,7*2147483647,row,limb);
 let out=NIH_scan_step(table,flag,row,limb);
 assert_eq!(out.0,expected.0 ^ cfg!(NIH_invert));assert_eq!(out.1,expected.1);assert_eq!(out.2,expected.2);assert_eq!(out.3,expected.3);
}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NDE_packed_after(){
 let table:[[u64;4];4]=kani::any();
 kani::assume(table[0][0]<7*2147483647&&table[0][1]<7*2147483647&&table[0][2]<7*2147483647&&table[0][3]<7*2147483647&&table[1][0]<7*2147483647&&table[1][1]<7*2147483647&&table[1][2]<7*2147483647&&table[1][3]<7*2147483647&&table[2][0]<7*2147483647&&table[2][1]<7*2147483647&&table[2][2]<7*2147483647&&table[2][3]<7*2147483647&&table[3][0]<7*2147483647&&table[3][1]<7*2147483647&&table[3][2]<7*2147483647&&table[3][3]<7*2147483647);
 let k:usize=kani::any();kani::assume(k<4);
 let expected=reference::packed_after_ref(table,7*2147483647);
 let out=NIH_packed_suffix(table);
 assert_eq!(out[k],expected[k] ^ if cfg!(NIH_invert){1}else{0});
}
