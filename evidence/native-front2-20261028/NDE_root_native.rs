pub(super) static mut NDE_ROOT_INDEX:usize=0;
#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::empty_root)]
fn NDE_empty_root(){
 let level:usize=kani::any();let j:usize=kani::any();kani::assume(level<21&&j<8);
 unsafe{NDE_ROOT_INDEX=j;}let _=super::empty_root(level);
}
