use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof]#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NCA_append_live_one(){
 let round:bool=kani::any();let i:usize=kani::any();let width=if round{224}else{32};kani::assume(i<width);let base=if round{32}else{0};let n=base+i;
 let source:[u8;224]=kani::any();let mut storage=Box::new([core::mem::MaybeUninit::<u8>::uninit();256]);
 // Harness-only construction of an arbitrary VALID live prefix. Spare capacity stays uninitialized.
 let mut j=0;while j<n{storage[j].write(kani::any());j+=1;}
 let ptr=Box::into_raw(storage) as *mut u8;let k:usize=kani::any();kani::assume(k<=n);let before=if k<n{unsafe{ptr.add(k).read()}}else{0};
 let mut out=unsafe{alloc::vec::Vec::from_raw_parts(ptr,n,256)};
 out.reserve(width-i);assert_eq!(out.as_ptr(),ptr);assert_eq!(out.len(),n);assert_eq!(out.capacity(),256);
 // ONE native iteration of the unchanged KMX extend loop on the actual Vec carrier.
 out.push(source[i]);assert_eq!(out.len(),n+1);assert_eq!(out.capacity(),256);assert_eq!(out.as_ptr(),ptr);assert_eq!(out[k],if k==n{source[i]}else{before});
 kani::cover!(round&&i==223,"last round1 append iteration");kani::cover!(!round&&i==31,"last root append iteration");
}
#[kani::proof]#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NCA_append_live_wrong(){
 let i:usize=kani::any();kani::assume(i<224);let n=32+i;let source:[u8;224]=kani::any();let mut storage=Box::new([core::mem::MaybeUninit::<u8>::uninit();256]);let mut j=0;while j<n{storage[j].write(kani::any());j+=1;}
 let ptr=Box::into_raw(storage) as *mut u8;let mut out=unsafe{alloc::vec::Vec::from_raw_parts(ptr,n,256)};kani::assume(source[i]==1);out.reserve(224-i);out.push(source[i]);assert_eq!(out[n],0,"negative last appended value is zero");
}
