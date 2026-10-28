use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));

static mut NCA_INPUT:*const u8=core::ptr::null();
static mut NCA_OUTPUT:*mut u8=core::ptr::null_mut();
static mut NCA_SRC:usize=0;
static mut NCA_DST:usize=0;
static mut NCA_SIZE:usize=0;
fn NCA_src(row:usize)->usize{if row<=2{32+5*row}else if row<=14{64+5*row}else if row<=25{155+453*(row-15)}else if row==26{6546}else{7015}}
fn NCA_dst(row:usize)->usize{if row<=2{32+5*row}else if row<=14{64+5*row}else if row<=25{171+901*(row-15)}else if row==26{12898}else{13831}}
fn NCA_expand_cut(input:&[u8],out:&mut[u8])->Result<(),CodecError>{unsafe{
 assert_eq!(input.as_ptr(),NCA_INPUT.add(NCA_SRC+5));assert_eq!(input.len(),NCA_SIZE/2);
 assert_eq!(out.as_mut_ptr(),NCA_OUTPUT.add(NCA_DST+5));assert_eq!(out.len(),NCA_SIZE);
 assert_eq!(input.len()%16,0);assert_eq!(out.len(),2*input.len());assert!(input.len()<=1856);
 kani::cover!(true,"same row reaches expansion with proved full callee domain");kani::assume(false);Ok(())
}}
// Frozen expand_semantic loop body after selecting its genuine row.
fn NCA_row(compact:&[u8],out:&mut[u8],row:u8,mut src:usize,mut dst:usize)->Result<(usize,usize),CodecError>{
 let size=crate::r1_wire::row_shape(row).ok_or(CodecError::Length)?.1;
 out[dst..dst+5].copy_from_slice(&compact[src..src+5]);src+=5;dst+=5;
 if row>=14{
  compact::expand_values(&compact[src..src+size/2],&mut out[dst..dst+size])?;src+=size/2;
 }else{out[dst..dst+size].copy_from_slice(&compact[src..src+size]);src+=size;}
 dst+=size;Ok((src,dst))
}
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(crate::compact::expand_values,NCA_expand_cut)]
fn NCA_semantic_compact_cut(){
 let input:[u8;7015]=kani::any();let mut out:[u8;13831]=kani::any();
 let row:u8=kani::any();kani::assume(row>=14&&row<27);let r=row as usize;let size=crate::r1_wire::row_shape(row).unwrap().1;
 unsafe{NCA_INPUT=input.as_ptr();NCA_OUTPUT=out.as_mut_ptr();NCA_SRC=NCA_src(r);NCA_DST=NCA_dst(r);NCA_SIZE=size;}
 let _=NCA_row(&input,&mut out,row,NCA_src(r),NCA_dst(r));assert!(false,"expansion call cut terminates all paths");
}
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::proof] #[kani::unwind(35)]
fn NCA_semantic_ordinary_row2(){
 let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();
 let row:u8=kani::any();kani::assume(row<14&&row==2);let r=row as usize;
 let src=NCA_src(r);let dst=NCA_dst(r);let size=crate::r1_wire::row_shape(row).unwrap().1;
 let j:usize=kani::any();kani::assume(j<134);let old=out[j];
 let result=NCA_row(&input,&mut out,row,src,dst);
 assert_eq!(result,Ok((NCA_src(r+1),NCA_dst(r+1))));
 assert_eq!(out[j],if j>=dst&&j<dst+5+size{input[src+j-dst]}else{old});
 kani::cover!(true,"noncompact payload and header copied on same carrier");
}

#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::proof] #[kani::unwind(35)]
fn NCA_row2_strong_control(){
 let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[78]==1);out[78]=0;
 let row:u8=kani::any();kani::assume(row<14&&row==2);let r=row as usize;
 let src=NCA_src(r);let dst=NCA_dst(r);let size=crate::r1_wire::row_shape(row).unwrap().1;
 let j:usize=kani::any();kani::assume(j<134);let old=out[j];
 let result=NCA_row(&input,&mut out,row,src,dst);
 assert_eq!(result,Ok((NCA_src(r+1),NCA_dst(r+1))));
 assert_eq!(out[78],0,"wrong unchanged row2 last payload byte");
 kani::cover!(true,"noncompact payload and header copied on same carrier");
}
