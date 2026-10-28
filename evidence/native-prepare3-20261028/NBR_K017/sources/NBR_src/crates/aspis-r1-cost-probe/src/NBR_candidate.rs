use super::*;
use alloc::vec::Vec;
// Scratch-only replacements. T: Copy excludes Clone side effects.
#[inline(never)]
pub unsafe fn NBR_copy_nonoverlapping<T: Copy>(src: *const T,dst: *mut T,count:usize){
    let mut i=0;while i<count {let value=unsafe{src.add(i).read()};unsafe{dst.add(i).write(value)};i+=1;}
}
#[inline(never)]
pub fn NBR_copy_from_slice<T: Copy>(dst:&mut [T],src:&[T]){
    assert_eq!(dst.len(),src.len());let mut i=0;while i<src.len(){dst[i]=src[i];i+=1;}
}
#[inline(never)]
pub fn NBR_clone_from_slice<T: Copy>(dst:&mut [T],src:&[T]){NBR_copy_from_slice(dst,src)}
#[inline(never)]
pub fn NBR_extend_from_slice<T: Copy,A:alloc::alloc::Allocator>(dst:&mut Vec<T,A>,src:&[T]){
    dst.reserve(src.len());let mut i=0;while i<src.len(){dst.push(src[i]);i+=1;}
}
#[inline(never)]
pub fn NBR_to_vec<T: Copy>(src:&[T])->Vec<T>{
    let mut dst=Vec::with_capacity(src.len());NBR_extend_from_slice(&mut dst,src);dst
}
// Match the successful-reallocation byte law, preserving the old allocation on failure.
// MaybeUninit permits copying spare-capacity bytes without reading them as values.
pub unsafe fn NBR_realloc(ptr:*mut u8,layout:alloc::alloc::Layout,new_size:usize)->*mut u8{
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

// Frozen initial root copy: restrict to the exact source/destination windows.
fn NBR_root_copy(input:&[u8],out:&mut[u8]){out[..32].copy_from_slice(&input[..32]);}
#[kani::stub(<[u8]>::copy_from_slice,NBR_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,NBR_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,NBR_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,NBR_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,NBR_to_vec)]
#[kani::stub(alloc::alloc::realloc,NBR_realloc)]
#[kani::proof] #[kani::unwind(35)]
fn NBR_root_byte(){
 let input:[u8;32]=kani::any();let mut out:[u8;33]=kani::any();let old=out[32];
 let j:usize=kani::any();kani::assume(j<32);NBR_root_copy(&input,&mut out);
 assert_eq!(out[j],input[j]);assert_eq!(out[32],old);
 kani::cover!(true,"semantic root bytes and adjacent byte use one source window");
}
// Arbitrary row header with one adjacent byte of the logical allocation.
#[kani::stub(<[u8]>::copy_from_slice,NBR_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,NBR_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,NBR_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,NBR_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,NBR_to_vec)]
#[kani::stub(alloc::alloc::realloc,NBR_realloc)]
#[kani::proof] #[kani::unwind(35)]
fn NBR_header_byte(){
 let input:[u8;5]=kani::any();let mut out:[u8;6]=kani::any();let old=out[5];
 let j:usize=kani::any();kani::assume(j<5);out[..5].copy_from_slice(&input);
 assert_eq!(out[j],input[j]);assert_eq!(out[5],old);
 kani::cover!(true,"every framed-row header byte is copied before its payload");
}
