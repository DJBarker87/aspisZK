pub(super) static mut NDE_PACKED_TABLE:[[u64;4];4]=[[0;4];4];
pub(super) static mut NDE_PACKED_ROW:usize=0;
pub(super) static mut NDE_PACKED_LIMB:usize=0;
pub(super) static mut NDE_PACKED_FLAG:bool=true;
pub(super) static mut NDE_MATRIX_REPLY:u64=0;
pub(super) static mut NDE_MATRIX_COUNT:usize=0;
pub(super) static mut NDE_SCAN_REPLY:(bool,usize,usize,bool)=(false,0,0,false);
#[cfg(NDE_matrix_step)]
#[kani::proof]
#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_matrix_cell(){
 let input:[QM31;4]=kani::any();
 for q in input{kani::assume(q.c0.a.0<0x7fff_ffff&&q.c0.b.0<0x7fff_ffff&&q.c1.a.0<0x7fff_ffff&&q.c1.b.0<0x7fff_ffff);}
 let row:usize=kani::any();let limb:usize=kani::any();kani::assume(row<4&&limb<4);
 unsafe{NDE_PACKED_ROW=row;NDE_PACKED_LIMB=limb;NDE_MATRIX_COUNT=0;}
 let cell=|q:QM31|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0][limb];
 let expected=reference::matrix_cell_ref(cell(input[0]),cell(input[1]),cell(input[2]),cell(input[3]),row);
 let _=super::external_local_packed_raw(input);
 assert!(unsafe{(NDE_MATRIX_COUNT==1&&NDE_MATRIX_REPLY==expected) != cfg!(NDE_window_invert)});
}
#[cfg(NDE_scan_step)]
#[kani::proof]
#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_scan_cell(){
 let table:[[u64;4];4]=kani::any();let flag:bool=kani::any();let row:usize=kani::any();let limb:usize=kani::any();kani::assume(row<4&&limb<=4);
 unsafe{NDE_PACKED_TABLE=table;NDE_PACKED_ROW=row;NDE_PACKED_LIMB=limb;NDE_PACKED_FLAG=flag;}
 let cell=if limb<4{table[row][limb]}else{0};
 let expected=reference::scan_step_ref(flag,cell,7*2147483647,row,limb);
 let _=super::external_local_packed_raw([QM31::ZERO;4]);
 assert!(unsafe{(NDE_SCAN_REPLY==expected) != cfg!(NDE_window_invert)});
}
#[cfg(NDE_packed_after)]
#[kani::proof]
#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_packed_after(){
 let table:[[u64;4];4]=kani::any();for row in table{for cell in row{kani::assume(cell<7*2147483647);}}
 let k:usize=kani::any();kani::assume(k<4);unsafe{NDE_PACKED_TABLE=table;}
 let expected=reference::packed_after_ref(table,7*2147483647);
 let out=super::external_local_packed_raw([QM31::ZERO;4]);
 assert!((out[k]==expected[k]) != cfg!(NDE_window_invert));
}
