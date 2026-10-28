pub(super) static mut NDE_SUM_PRE:QM31=QM31::ZERO;
pub(super) static mut NDE_SUM_STEPPED:bool=false;
pub(super) static mut NDE_RECON_DONE:bool=false;
#[cfg(NDE_sum_step)]
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_sum_step(){
 let raw:[[u32;4];64]=kani::any();let high=raw.map(|a|to_native(reference::Q{c0:reference::C{a:a[0],b:a[1]},c1:reference::C{a:a[2],b:a[3]}}));
 let raw_low:[[u32;4];16]=kani::any();let low=raw_low.map(|a|to_native(reference::Q{c0:reference::C{a:a[0],b:a[1]},c1:reference::C{a:a[2],b:a[3]}}));
 let selectors=Selectors{high,low};
 let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<=end&&end<=64);
 let pre=anyq();kani::assume(canonical(pre));
 let expected=if start<end{let q=selectors.high[start];kani::assume(canonical(q));to_native(reference::sum_step_ref(to_ref(pre),to_ref(q)))}else{pre};
 unsafe{NDE_SUM_PRE=pre;NDE_SUM_STEPPED=false;}
 let out=super::sum_high(&selectors,&[start..end]);
 let stepped=unsafe{NDE_SUM_STEPPED};
 assert!((out==expected&&stepped==(start<end)) != cfg!(NDE_invert));
}
#[cfg(NDE_reconstruct_step)]
#[kani::proof]
#[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_reconstruct_step(){
 let raw:[[u32;4];16]=kani::any();let view=raw.map(|a|to_native(reference::Q{c0:reference::C{a:a[0],b:a[1]},c1:reference::C{a:a[2],b:a[3]}}));
 kani::assume(canonical(view[9])&&canonical(view[8]));
 unsafe{NDE_RECON_DONE=false;}
 let expected=to_native(reference::reconstruct_step_ref(to_ref(view[9]),to_ref(view[8])));
 let out=super::reconstruct_10(&view);
 assert!((out==expected&&unsafe{NDE_RECON_DONE}) != cfg!(NDE_invert));
}
