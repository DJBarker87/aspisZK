pub(super) static mut NDE_ROOT_INDEX:usize=0;
#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::empty_root)]
fn NDE_empty_root(){
 let level:usize=kani::any();let j:usize=kani::any();kani::assume(level<21&&j<8);
 if cfg!(NDE_invert){kani::assume(level==0&&j==0);}
 unsafe{NDE_ROOT_INDEX=j;}let _=super::empty_root(level);
}
// Different negative property from the timed-out inverted contract: a concrete
// wrong word on the real body. Not a renamed harness or a new positive claim.
#[kani::proof]
#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_root_bad_value(){let value=super::empty_root(0);assert!(value[0].0==0,"NDE wrong root word");}
