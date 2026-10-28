use alloc::vec::Vec;
// Scratch-only replacements. T: Copy excludes Clone side effects.
#[inline(never)]
pub unsafe fn KMX_copy_nonoverlapping<T: Copy>(src: *const T,dst: *mut T,count:usize){
    let mut i=0;while i<count {let value=unsafe{src.add(i).read()};unsafe{dst.add(i).write(value)};i+=1;}
}
#[inline(never)]
pub fn KMX_copy_from_slice<T: Copy>(dst:&mut [T],src:&[T]){
    assert_eq!(dst.len(),src.len());let mut i=0;while i<src.len(){dst[i]=src[i];i+=1;}
}
#[inline(never)]
pub fn KMX_clone_from_slice<T: Copy>(dst:&mut [T],src:&[T]){KMX_copy_from_slice(dst,src)}
#[inline(never)]
pub fn KMX_extend_from_slice<T: Copy,A:alloc::alloc::Allocator>(dst:&mut Vec<T,A>,src:&[T]){
    dst.reserve(src.len());let mut i=0;while i<src.len(){dst.push(src[i]);i+=1;}
}
#[inline(never)]
pub fn KMX_to_vec<T: Copy>(src:&[T])->Vec<T>{
    let mut dst=Vec::with_capacity(src.len());KMX_extend_from_slice(&mut dst,src);dst
}
// Match the successful-reallocation byte law, preserving the old allocation on failure.
// MaybeUninit permits copying spare-capacity bytes without reading them as values.
pub unsafe fn KMX_realloc(ptr:*mut u8,layout:alloc::alloc::Layout,new_size:usize)->*mut u8{
 let new_layout=alloc::alloc::Layout::from_size_align(new_size,layout.align()).unwrap();
 let out=unsafe{alloc::alloc::alloc(new_layout)};
 if !out.is_null(){
  let mut i=0;while i<core::cmp::min(layout.size(),new_size){
   let value=unsafe{ptr.cast::<core::mem::MaybeUninit<u8>>().add(i).read()};
   unsafe{out.cast::<core::mem::MaybeUninit<u8>>().add(i).write(value)};i+=1;
  }
  unsafe{alloc::alloc::dealloc(ptr,layout)};
 }
 out
}
#[cfg(kani)]
mod KMX_checks{
use super::*;
#[kani::proof] #[kani::unwind(18)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn KMX_slice_correct(){let src:[u32;16]=kani::any();let mut dst=[0u32;16];dst.copy_from_slice(&src);let k:usize=kani::any();kani::assume(k<16);assert_eq!(dst[k],src[k]);}
#[kani::proof] #[kani::unwind(18)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn KMX_slice_wrong(){let mut src=[0u32;16];src[15]=512;let mut dst=[0u32;16];dst.copy_from_slice(&src);assert_eq!(dst[15],0);}
#[kani::proof] #[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn KMX_ptr_correct(){let src:[u32;16]=kani::any();let mut dst=[0u32;16];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),16)};let k:usize=kani::any();kani::assume(k<16);assert_eq!(dst[k],src[k]);}
#[kani::proof] #[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn KMX_ptr_wrong(){let mut src=[0u32;16];src[15]=512;let mut dst=[0u32;16];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),16)};assert_eq!(dst[15],0);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(<[u32]>::clone_from_slice,KMX_clone_from_slice)]
fn KMX_clone_correct(){let src:[u32;16]=kani::any();let mut dst=[0u32;16];dst.clone_from_slice(&src);let k:usize=kani::any();kani::assume(k<16);assert_eq!(dst[k],src[k]);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(<[u32]>::clone_from_slice,KMX_clone_from_slice)]
fn KMX_clone_wrong(){let mut src=[0u32;16];src[15]=512;let mut dst=[0u32;16];dst.clone_from_slice(&src);assert_eq!(dst[15],0);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Vec::<u32>::extend_from_slice,KMX_extend_from_slice)]
fn KMX_extend_correct(){let src:[u32;16]=kani::any();let mut dst=Vec::with_capacity(16);dst.extend_from_slice(&src);let k:usize=kani::any();kani::assume(k<16);assert_eq!(dst[k],src[k]);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(Vec::<u32>::extend_from_slice,KMX_extend_from_slice)]
fn KMX_extend_wrong(){let mut src=[0u32;16];src[15]=512;let mut dst=Vec::with_capacity(16);dst.extend_from_slice(&src);assert_eq!(dst[15],0);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(<[u32]>::to_vec,KMX_to_vec)]
fn KMX_to_vec_correct(){let src:[u32;16]=kani::any();let dst=src.to_vec();let k:usize=kani::any();kani::assume(k<16);assert_eq!(dst[k],src[k]);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(<[u32]>::to_vec,KMX_to_vec)]
fn KMX_to_vec_wrong(){let mut src=[0u32;16];src[15]=512;let dst=src.to_vec();assert_eq!(dst[15],0);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn KMX_growth_correct(){let src:[u32;16]=kani::any();let mut dst=Vec::with_capacity(1);dst.push(7u32);for x in src {dst.push(x);}let k:usize=kani::any();kani::assume(k<16);assert_eq!(dst[k+1],src[k]);}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn KMX_growth_wrong(){let mut src=[0u32;16];src[15]=512;let mut dst=Vec::with_capacity(1);dst.push(7u32);for x in src {dst.push(x);}assert_eq!(dst[16],0);}
}
