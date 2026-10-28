use super::*;
static mut NBR_INPUT:*const u8=core::ptr::null();
static mut NBR_OUTPUT:*mut u8=core::ptr::null_mut();
static mut NBR_SRC:usize=0;
static mut NBR_DST:usize=0;
static mut NBR_SIZE:usize=0;
fn NBR_src(row:usize)->usize{if row<=2{32+5*row}else if row<=14{64+5*row}else if row<=25{155+453*(row-15)}else if row==26{6546}else{7015}}
fn NBR_dst(row:usize)->usize{if row<=2{32+5*row}else if row<=14{64+5*row}else if row<=25{171+901*(row-15)}else if row==26{12898}else{13831}}
fn NBR_expand_cut(input:&[u8],out:&mut[u8])->Result<(),CodecError>{unsafe{
 assert_eq!(input.as_ptr(),NBR_INPUT.add(NBR_SRC+5));assert_eq!(input.len(),NBR_SIZE/2);
 assert_eq!(out.as_mut_ptr(),NBR_OUTPUT.add(NBR_DST+5));assert_eq!(out.len(),NBR_SIZE);
 assert_eq!(input.len()%16,0);assert_eq!(out.len(),2*input.len());assert!(input.len()<=1856);
 kani::cover!(true,"same row reaches expansion with proved full callee domain");kani::assume(false);Ok(())
}}
// Frozen expand_semantic loop body after selecting its genuine row.
fn NBR_row(compact:&[u8],out:&mut[u8],row:u8,mut src:usize,mut dst:usize)->Result<(usize,usize),CodecError>{
 let size=crate::r1_wire::row_shape(row).ok_or(CodecError::Length)?.1;
 out[dst..dst+5].copy_from_slice(&compact[src..src+5]);src+=5;dst+=5;
 if row>=14{
  compact::expand_values(&compact[src..src+size/2],&mut out[dst..dst+size])?;src+=size/2;
 }else{out[dst..dst+size].copy_from_slice(&compact[src..src+size]);src+=size;}
 dst+=size;Ok((src,dst))
}
#[kani::proof] #[kani::unwind(2)]
#[kani::stub(crate::compact::expand_values,NBR_expand_cut)]
fn NBR_semantic_compact_cut(){
 let input:[u8;7015]=kani::any();let mut out:[u8;13831]=kani::any();
 let row:u8=kani::any();kani::assume(row>=14&&row<27);let r=row as usize;let size=crate::r1_wire::row_shape(row).unwrap().1;
 unsafe{NBR_INPUT=input.as_ptr();NBR_OUTPUT=out.as_mut_ptr();NBR_SRC=NBR_src(r);NBR_DST=NBR_dst(r);NBR_SIZE=size;}
 let _=NBR_row(&input,&mut out,row,NBR_src(r),NBR_dst(r));assert!(false,"expansion call cut terminates all paths");
}
#[kani::proof] #[kani::unwind(2)]
fn NBR_semantic_ordinary_prefix(){
 let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();
 let row:u8=kani::any();kani::assume(row<14);let r=row as usize;
 let src=NBR_src(r);let dst=NBR_dst(r);let size=crate::r1_wire::row_shape(row).unwrap().1;
 let j:usize=kani::any();kani::assume(j<134);let old=out[j];
 let result=NBR_row(&input,&mut out,row,src,dst);
 assert_eq!(result,Ok((NBR_src(r+1),NBR_dst(r+1))));
 assert_eq!(out[j],if j>=dst&&j<dst+5+size{input[src+j-dst]}else{old});
 kani::cover!(row==2,"noncompact payload and header copied on same carrier");
}
