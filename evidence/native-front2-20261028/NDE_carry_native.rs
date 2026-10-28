#[cfg(NDE_carry_step)] pub(super) static mut NDE_CARRY:usize=0;
#[cfg(NDE_carry_step)] pub(super) static mut NDE_NEXT_INDEX:u64=0;
#[cfg(NDE_carry_step)] pub(super) static mut NDE_CONTINUE:bool=false;
#[cfg(NDE_carry_step)] pub(super) fn carry_record(index:u64){unsafe{NDE_NEXT_INDEX=index;NDE_CONTINUE=true;}}
#[cfg(NDE_carry_step)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof]
#[kani::unwind(2)]
fn NDE_carry_step(){
 let index:u64=kani::any();let carry:usize=kani::any();
 unsafe{NDE_CARRY=carry;NDE_NEXT_INDEX=index;NDE_CONTINUE=false;}
 let result=super::bounded_append_carry(index);
 let step=unsafe{(NDE_NEXT_INDEX,result,NDE_CONTINUE)};
 assert!((step==reference::carry_step_ref(index,carry)) != cfg!(NDE_invert));
}
