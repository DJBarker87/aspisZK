use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
const MODE:usize=0;const ROW:usize=0;const SRC:usize=32;const DST:usize=32;
const PAYLOAD:usize=0;const STORED:usize=0;
const INPUT_START:usize=48;const INPUT_WIDTH:usize=5;
const OUTPUT_START:usize=32;const OUTPUT_WIDTH:usize=5;
#[repr(C)] struct ProofBacking{prefix:[u8;INPUT_START],window:[u8;INPUT_WIDTH],suffix:[u8;57607-INPUT_START-INPUT_WIDTH]}
#[repr(C)] struct LogicalBacking{prefix:[u8;OUTPUT_START],window:[u8;OUTPUT_WIDTH],suffix:[u8;13794],y1:[u8;928]}
fn expected(input:&[u8],cell:usize)->u8{
 if MODE==2 {return if cell%32<16{input[(cell/32)*16+cell%32]}else{0};}
 if MODE==1 {return input[cell];}
 if cell<5{return input[SRC+cell];}
 let j=cell-5;
 if ROW<14{return input[SRC+5+j];}
 if j%32<16{input[SRC+5+(j/32)*16+j%32]}else{0}
}
struct Log{proof:usize,logical:usize,calls:usize,cell:usize,reply:u8}
impl Log{
 fn expand(&mut self,input:&[u8],out:&mut[u8])->Result<(),compact::CodecError>{
  self.calls+=1;
  if MODE==2{assert!(input.as_ptr() as usize==self.proof+7031&&input.len()==464&&out.as_ptr() as usize==self.logical+13831&&out.len()==928);}
  else{assert!(input.as_ptr() as usize==self.proof+16&&input.len()==7015&&out.as_ptr() as usize==self.logical&&out.len()==13831);}
  self.reply=expected(input,self.cell);
  let selected=if MODE==2{self.cell}else{OUTPUT_START+self.cell};
  out[selected]=if cfg!(NHF_bad_expand){self.reply^1}else{self.reply};
  // Full closed-packet projection on these exact dimensions always succeeds.
  Ok(())
 }
}
fn semantic_cut(proof:&[u8],logical:&mut[u8],log:&mut Log)->Result<(),Error>{
 let (semantic,_y1)=logical.split_at_mut(compact::LOGICAL_SEMANTIC);
 log.expand(&proof[compact::OFF_SEMANTIC+usize::from(cfg!(NHF_bad_stage))..compact::OFF_Y1],semantic)?;
 Ok(())
}
fn values_cut(proof:&[u8],logical:&mut[u8],log:&mut Log)->Result<(),Error>{
 let (_semantic,y1)=logical.split_at_mut(compact::LOGICAL_SEMANTIC);
 log.expand(&proof[compact::OFF_Y1+usize::from(cfg!(NHF_bad_stage))..compact::OFF_INACTIVE],y1)?;
 Ok(())
}
fn check_window(){
 let proof_backing=ProofBacking{prefix:kani::any(),window:kani::any(),suffix:kani::any()};
 let mut logical_backing=LogicalBacking{prefix:kani::any(),window:kani::any(),suffix:kani::any(),y1:kani::any()};
 assert_eq!(core::mem::size_of::<ProofBacking>(),57607);assert_eq!(core::mem::align_of::<ProofBacking>(),1);
 assert_eq!(core::mem::offset_of!(ProofBacking,window),INPUT_START);
 assert_eq!(core::mem::size_of::<LogicalBacking>(),14759);assert_eq!(core::mem::align_of::<LogicalBacking>(),1);
 assert_eq!(core::mem::offset_of!(LogicalBacking,window),OUTPUT_START);
 let proof=unsafe{core::slice::from_raw_parts((&proof_backing as *const ProofBacking).cast::<u8>(),57607)};
 let logical=unsafe{core::slice::from_raw_parts_mut((&mut logical_backing as *mut LogicalBacking).cast::<u8>(),14759)};
 let cell:usize=kani::any();kani::assume(cell<OUTPUT_WIDTH);
 let observe=OUTPUT_START+cell;
 let frame:usize=kani::any();kani::assume(frame<(if MODE==2{13831}else{928}));
 let frame_index=if MODE==2{frame}else{13831+frame};let before=logical[frame_index];
 let source=if MODE==2{&proof[7031..7495]}else{&proof[16..7031]};
 let wanted=expected(source,cell);
 let mut log=Log{proof:proof.as_ptr() as usize,logical:logical.as_ptr() as usize,calls:0,cell,reply:0};
 let result=if MODE==2{values_cut(proof,logical,&mut log)}else{semantic_cut(proof,logical,&mut log)};
 assert!(result.is_ok());assert!(log.calls==1);assert!(log.reply==wanted);
 assert!(logical[observe]==wanted);assert!(logical[frame_index]==before);
 if MODE==0{kani::cover!(cell<5);if PAYLOAD>0{kani::cover!(cell>=5);}}
 else{kani::cover!(cell==0);kani::cover!(cell+1==OUTPUT_WIDTH);}
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn semantic_stage(){check_window()}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn values_stage(){check_window()}
