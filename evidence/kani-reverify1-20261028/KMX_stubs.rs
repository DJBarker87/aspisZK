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
