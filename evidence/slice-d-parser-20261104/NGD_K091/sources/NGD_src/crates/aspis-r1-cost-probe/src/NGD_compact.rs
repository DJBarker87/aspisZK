use super::*;
#[kani::proof] #[kani::unwind(8)]
fn slot_all(){
 let slot:usize=kani::any();kani::assume(slot<=6);
 let result=slot_offset(slot);
 let expected=match slot{0=>28359,1=>33031,2=>37703,3=>41799,4=>47303,5=>52807,_=>57607};
 assert!((result==expected) != cfg!(NGD_invert));
}
#[kani::proof] #[kani::unwind(2)]
fn slot_native_step(){
 let i:usize=kani::any();let at:usize=kani::any();kani::assume(i<6&&at<=57607);
 let mut next=at;next+=32*SLOT_NODES[i];let j=i+1;
 assert!((next==at+match i{0|1=>4672,2=>4096,3|4=>5504,_=>4800}&&j<=6&&next<=63111) != cfg!(NGD_invert));
}

pub(super) fn slot_reference(slot:usize)->usize{let mut at=OFF_NODES;let mut i=0;while i<slot{at+=32*SLOT_NODES[i];i+=1;}at}
#[kani::proof_for_contract(slot_offset)] #[kani::unwind(8)]
fn slot_contract(){let slot:usize=kani::any();kani::assume(slot<=6);let _=slot_offset(slot);}

include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn src_cursor(r:u8)->usize{let r=r as usize;if r<=2{32+5*r}else if r<=14{64+5*r}else if r<=25{155+453*(r-15)}else if r==26{6546}else{7015}}
fn dst_cursor(r:u8)->usize{let r=r as usize;if r<=2{32+5*r}else if r<=14{64+5*r}else if r<=25{171+901*(r-15)}else if r==26{12898}else{13831}}
// Data-independent control projection of the frozen original loop. Data
// operations are cuts, never substituted values. There are exactly 27 rows.
fn native_semantic_control(cut:u8)->Result<(usize,usize,usize,usize,usize),CodecError>{
 let(mut src,mut dst)=(32,32);let(mut seen_src,mut seen_dst,mut seen_size,mut calls)=(0,0,0,0);
 for row in 0..SEMANTIC_ROWS{
  let size=row_shape(row).ok_or(CodecError::Length)?.1;
  if row==cut{seen_src=src;seen_dst=dst;seen_size=size;}
  calls+=1;
  src+=5;dst+=5;
  if compact_row(row){src+=size/2;}else{src+=size;}
  dst+=size;
 }
 if src!=COMPACT_SEMANTIC||dst!=LOGICAL_SEMANTIC{return Err(CodecError::Length);}
 Ok((seen_src,seen_dst,seen_size,calls,src+dst))
}
#[kani::proof] #[kani::unwind(29)]
fn semantic_control(){let row:u8=kani::any();kani::assume(row<27);let r=native_semantic_control(row);
 let mut expected=src_cursor(row);if cfg!(NGD_invert){expected+=1;}
 assert_eq!(r,Ok((expected,dst_cursor(row),row_shape(row).unwrap().1,27,20846)));
}
// Initial copy observed in a bounded same-allocation frame; all bytes arbitrary.
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn semantic_initial_copy(){let src:[u8;32]=kani::any();let mut out:[u8;96]=kani::any();let j:usize=kani::any();kani::assume(j<96);let old=out[j];out[..32].copy_from_slice(&src);assert!((out[j]==if j<32{src[j]}else{old}) != cfg!(NGD_invert));}
struct Window{reply:Result<(),CodecError>,input:*const u8,output:*const u8,input_len:usize,output_len:usize,calls:usize,observed:usize,start:usize,after:u8,before:u8,inside:bool}
fn expand_capture(input:&[u8],out:&mut[u8],log:&mut Window)->Result<(),CodecError>{
 log.input=input.as_ptr();log.output=out.as_ptr();log.input_len=input.len();log.output_len=out.len();log.calls+=1;
 log.inside=log.start<=log.observed&&log.observed<log.start+out.len();
 if log.inside{let j=log.observed-log.start;log.before=out[j];out[j]=log.after;}
 log.reply
}
// One frozen row body, arbitrary prestate. Child mutation is the selected
// coordinate projection; completion needs the stated Lean projection/frame law.
fn native_semantic_step(input:&[u8],out:&mut[u8],row:u8,src:&mut usize,dst:&mut usize,log:&mut Window)->Result<(),CodecError>{
 let size=row_shape(row).ok_or(CodecError::Length)?.1;
 out[*dst..*dst+5].copy_from_slice(&input[*src..*src+5]);*src+=5;*dst+=5;
 if compact_row(row){expand_capture(&input[*src..*src+size/2],&mut out[*dst..*dst+size],log)?;*src+=size/2;}
 else{out[*dst..*dst+size].copy_from_slice(&input[*src..*src+size]);*src+=size;}
 *dst+=size;Ok(())
}
fn semantic_cut(row:u8,group:u8){
 let input:[u8;7015]=kani::any();let mut out:[u8;13831]=kani::any();let j:usize=kani::any();kani::assume(j<13831);let old=out[j];let base=out.as_ptr();
 let src0=src_cursor(row);let dst0=dst_cursor(row);let size=row_shape(row).unwrap().1;
 let reply=match kani::any::<u8>()%4{0=>Ok(()),1=>Err(CodecError::Length),2=>Err(CodecError::NonZeroHigh),_=>Err(CodecError::NonCanonical)};
 let after:u8=kani::any();let mut log=Window{reply,input:core::ptr::null(),output:core::ptr::null(),input_len:0,output_len:0,calls:0,observed:j,start:dst0+5,after,before:0,inside:false};
 let(mut src,mut dst)=(src0,dst0);let result=native_semantic_step(&input,&mut out,row,&mut src,&mut dst,&mut log);
 let stopped=row>=14&&reply.is_err();let result_ok=if row>=14{result==reply}else{result==Ok(())};
 let cursors=src==if stopped{src0+5}else{src_cursor(row+1)}&&dst==if stopped{dst0+5}else{dst_cursor(row+1)};
 let arguments=if row>=14{log.calls==1&&log.input==input.as_ptr().wrapping_add(src0+5)&&log.input_len==size/2&&log.output==base.wrapping_add(dst0+5)&&log.output_len==size&&(!log.inside||log.before==old)}else{log.calls==0};
 let expected=if dst0<=j&&j<dst0+5{input[src0+j-dst0]}else if dst0+5<=j&&j<dst0+5+size{if row>=14{after}else{input[src0+j-dst0]}}else{old};
 let metadata=if row>=14{log.calls==1&&log.input==input.as_ptr().wrapping_add(src0+5)&&log.input_len==size/2&&log.output==base.wrapping_add(dst0+5)&&log.output_len==size}else{log.calls==0};
 let good=if group==0{result_ok&&cursors&&arguments}else if group==2{result_ok&&cursors&&metadata}else{out[j]==expected};assert!(good != cfg!(NGD_invert));
}
macro_rules! semantic_gate{($name:ident,$row:expr,$g:expr)=>{#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){semantic_cut($row,$g)}};}
semantic_gate!(semantic_row14,14,0);
semantic_gate!(semantic_row15,15,0);
semantic_gate!(semantic_row16,16,0);
semantic_gate!(semantic_row17,17,0);
semantic_gate!(semantic_row18,18,0);
semantic_gate!(semantic_row19,19,0);
semantic_gate!(semantic_row20,20,0);
semantic_gate!(semantic_row21,21,0);
semantic_gate!(semantic_row22,22,0);
semantic_gate!(semantic_row23,23,0);
semantic_gate!(semantic_row24,24,0);
semantic_gate!(semantic_row25,25,0);
semantic_gate!(semantic_row26,26,0);
semantic_gate!(semantic_low_rows,2,0);semantic_gate!(semantic_row14_value,14,1);
semantic_gate!(semantic_row14_callsite,14,2);
semantic_gate!(semantic_row15_callsite,15,2);
semantic_gate!(semantic_row16_callsite,16,2);
semantic_gate!(semantic_row17_callsite,17,2);
semantic_gate!(semantic_row18_callsite,18,2);
semantic_gate!(semantic_row19_callsite,19,2);
semantic_gate!(semantic_row20_callsite,20,2);
semantic_gate!(semantic_row21_callsite,21,2);
semantic_gate!(semantic_row22_callsite,22,2);
semantic_gate!(semantic_row23_callsite,23,2);
semantic_gate!(semantic_row24_callsite,24,2);
semantic_gate!(semantic_row25_callsite,25,2);
semantic_gate!(semantic_row26_callsite,26,2);
semantic_gate!(semantic_low_callsite,2,2);

#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn semantic_low_all(){let row:u8=kani::any();kani::assume(row<14);semantic_cut(row,2);}
fn copy_frame<const N:usize>(){let input:[u8;N]=kani::any();let mut output:[u8;96]=kani::any();let at:usize=kani::any();kani::assume(at<=96-N);let j:usize=kani::any();kani::assume(j<96);let old=output[j];let ptr=output.as_ptr();output[at..at+N].copy_from_slice(&input);let expected=if at<=j&&j<at+N{input[j-at]}else{old};assert!((output[j]==expected&&output.as_ptr()==ptr) != cfg!(NGD_invert));}
macro_rules! copyframe{($name:ident,$n:expr)=>{#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){copy_frame::<$n>()}};}
copyframe!(semantic_header5_frame,5);copyframe!(semantic_payload32_frame,32);
