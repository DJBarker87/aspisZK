use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
const MODE:usize=0;const ROW:usize=15;const SRC:usize=155;const DST:usize=171;
const PAYLOAD:usize=896;const STORED:usize=448;
const INPUT_START:usize=171;const INPUT_WIDTH:usize=453;
const OUTPUT_START:usize=171;const OUTPUT_WIDTH:usize=901;
#[repr(C)] struct ProofBacking{prefix:[u8;INPUT_START],window:[u8;INPUT_WIDTH],suffix:[u8;57607-INPUT_START-INPUT_WIDTH]}
#[repr(C)] struct LogicalBacking{prefix:[u8;OUTPUT_START],window:[u8;OUTPUT_WIDTH],suffix:[u8;12759],y1:[u8;928]}
fn source_index(cell:usize)->Option<usize>{
 if MODE==2 {return if cell%32<16{Some((cell/32)*16+cell%32)}else{None};}
 if MODE==1 {return Some(cell);}
 if cell<5{return Some(cell);}
 let j=cell-5;
 if ROW<14{return Some(5+j);}
 if j%32<16{Some(5+(j/32)*16+j%32)}else{None}
}
struct Log{proof:usize,logical:usize,calls:usize,cell:usize,reply:u8,source_byte:u8,source_pointer:usize,modified_start:usize,modified_length:usize,selected:usize}
impl Log{
 fn expand(&mut self,input:&[u8],out:&mut[u8])->Result<(),compact::CodecError>{
  self.calls+=1;
  if MODE==2{assert!(input.as_ptr() as usize==self.proof+7031&&input.len()==464&&out.as_ptr() as usize==self.logical+13831&&out.len()==928);}
  else{assert!(input.as_ptr() as usize==self.proof+16&&input.len()==7015&&out.as_ptr() as usize==self.logical&&out.len()==13831);}
  self.reply=match source_index(self.cell){
   None=>0,
   Some(relative)=>{let base=if MODE==0{SRC}else{0};
    assert!(input.as_ptr() as usize+base+relative==self.source_pointer);
    self.source_byte}
  };
  let selected=if MODE==2{self.cell}else{OUTPUT_START+self.cell};
  self.modified_start=if MODE==2{13831}else{0};self.modified_length=out.len();self.selected=selected;
  if cfg!(NHF_bad_expand){self.reply^=1;}
  // Native cut records the CLOSED callee memory effect. It does not replay
  // those physical writes. K009/K011 supply the separate caller frame;
  // NGV packets supply the complete same-window byte update in Lean.
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
 let mut logical_backing:[u8;14759]=kani::any();
 assert_eq!(core::mem::size_of::<ProofBacking>(),57607);assert_eq!(core::mem::align_of::<ProofBacking>(),1);
 assert_eq!(core::mem::offset_of!(ProofBacking,window),INPUT_START);

 let proof=unsafe{core::slice::from_raw_parts((&proof_backing as *const ProofBacking).cast::<u8>(),57607)};
 let logical=&mut logical_backing[..];
 let cell:usize=kani::any();kani::assume(cell<OUTPUT_WIDTH);
 let observe=OUTPUT_START+cell;
 // Opposite-window arbitrary-prestate frame is separately K009/K011.
 // This independent obligation checks the full natural selected-byte reply.
 let source=if MODE==2{&proof[7031..7495]}else{&proof[16..7031]};
 let local=source_index(cell).unwrap_or(0);
 let source_byte=proof_backing.window[local];
 let source_pointer=&proof_backing.window[local] as *const u8 as usize;
 let wanted=if source_index(cell).is_some(){source_byte}else{0};
 let mut log=Log{proof:proof.as_ptr() as usize,logical:logical.as_ptr() as usize,calls:0,cell,reply:0,source_byte,source_pointer,modified_start:0,modified_length:0,selected:0};
 let result=if MODE==2{values_cut(proof,logical,&mut log)}else{semantic_cut(proof,logical,&mut log)};
 assert!(result.is_ok());assert!(log.calls==1);assert!(log.reply==wanted);
 assert!(log.reply==wanted);assert!(log.modified_start==(if MODE==2{13831}else{0}));assert!(log.modified_length==(if MODE==2{928}else{13831}));assert!(log.modified_start+log.selected==observe);
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
