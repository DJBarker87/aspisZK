use aspis_core::field::M31;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_iter_mut_active() {
 let mut state:[M31;16]=core::array::from_fn(|_|M31(kani::any()));
 let at:usize=kani::any();let k:usize=kani::any();let h:usize=kani::any();let reply=M31(kani::any());
 kani::assume(at<16&&k<16&&h<2);
 let base=state.as_mut_ptr();let before=state[k];let selected=state[at];
 let mut iter=state[at..].iter_mut();let value=iter.next().unwrap();
 let address=value as *mut M31;let observed=*value;*value=reply;
 let header:[usize;2]=unsafe{core::mem::transmute(iter)};
 let expected:[usize;2]=unsafe{core::mem::transmute(state[at+1..].iter_mut())};
 if cfg!(NJE_bad_argument){assert_eq!(header[h],expected[h]^1)}else{assert_eq!(header[h],expected[h])}
 assert_eq!(address,unsafe{base.add(at)});assert_eq!(observed,selected);
 assert_eq!(state[k],if k==at{reply}else{before});
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(140)]
fn NJE_iter_mut_exit() {
 let mut state:[M31;16]=core::array::from_fn(|_|M31(kani::any()));
 let k:usize=kani::any();kani::assume(k<16);let before=state[k];
 let mut iter=state[16..].iter_mut();let out=iter.next();
 if cfg!(NJE_bad_argument){assert!(out.is_some())}else{assert!(out.is_none())}
 assert_eq!(state[k],before);
}
