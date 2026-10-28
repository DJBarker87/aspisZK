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

#[kani::stub(<[u8]>::copy_from_slice,NBR_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,NBR_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,NBR_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,NBR_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,NBR_to_vec)]
#[kani::stub(alloc::alloc::realloc,NBR_realloc)]
#[kani::proof]#[kani::unwind(35)]
fn NBR_semantic_iterator(){
 let len:usize=kani::any();assert_eq!(NBR_shape_length(len).is_ok(),len==57607);
 let row:u8=kani::any();kani::assume(row<=27);let mut it=row..27;let got=it.next();
 if row<27{assert_eq!(got,Some(row));assert_eq!(it.start,row+1);assert_eq!(it.end,27);}else{assert_eq!(got,None);assert_eq!(it.start,27);assert_eq!(it.end,27);}
 kani::cover!(row==0,"first semantic row is selected");kani::cover!(row==27,"semantic loop stops before any extra row");
}
fn NBR_shape_length(len:usize)->Result<(),Error>{if len!=compact::PROOF_BYTES{return Err(Error::Parse);}Ok(())}
#[kani::stub(<[u8]>::copy_from_slice,NBR_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,NBR_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,NBR_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,NBR_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,NBR_to_vec)]
#[kani::stub(alloc::alloc::realloc,NBR_realloc)]
#[kani::proof]#[kani::unwind(35)]
fn NBR_shape_length_cut(){let len:usize=kani::any();let r=NBR_shape_length(len);assert_eq!(r.is_ok(),len==57607);kani::cover!(len!=57607,"length rejection precedes all header reads");}
fn NBR_semantic_end(src:usize,dst:usize,compact_len:usize,out_len:usize)->Result<(),CodecError>{if src!=compact_len||dst!=out_len{return Err(CodecError::Length);}Ok(())}
#[kani::stub(<[u8]>::copy_from_slice,NBR_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,NBR_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,NBR_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,NBR_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,NBR_to_vec)]
#[kani::stub(alloc::alloc::realloc,NBR_realloc)]
#[kani::proof]#[kani::unwind(35)]
fn NBR_semantic_end_cut(){let src:usize=kani::any();let dst:usize=kani::any();let r=NBR_semantic_end(src,dst,7015,13831);assert_eq!(r.is_ok(),src==7015&&dst==13831);kani::cover!(src==7015&&dst==13831,"the proved loop geometry supplies exact completion");}
fn NBR_after_values_return(returned:Result<(),CodecError>,mut src:usize,mut dst:usize,size:usize)->Result<(usize,usize),CodecError>{returned?;src+=size/2;dst+=size;Ok((src,dst))}
#[kani::stub(<[u8]>::copy_from_slice,NBR_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,NBR_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,NBR_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,NBR_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,NBR_to_vec)]
#[kani::stub(alloc::alloc::realloc,NBR_realloc)]
#[kani::proof]#[kani::unwind(35)]
fn NBR_semantic_values_return(){let row:u8=kani::any();kani::assume(row>=14&&row<27);let r=row as usize;let size=crate::r1_wire::row_shape(row).unwrap().1;let src:usize=kani::any();let dst:usize=kani::any();kani::assume(src<=7015-size/2&&dst<=13831-size);let choice:u8=kani::any();kani::assume(choice<4);let err=match choice{0=>CodecError::Length,1=>CodecError::NonZeroHigh,_=>CodecError::NonCanonical};let returned=if choice==3{Ok(())}else{Err(err)};let out=NBR_after_values_return(returned,src,dst,size);if choice==3{assert_eq!(out,Ok((src+size/2,dst+size)));}else{assert_eq!(out,Err(err));}kani::cover!(r==25&&choice==3,"largest compact row returns exact next positions");}
