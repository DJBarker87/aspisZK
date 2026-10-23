#[cfg(kani)] mod RealR3_context_proofs {
use super::*;
#[derive(Clone,Copy)] struct NoHash;
impl Digest32 for NoHash {fn digest(&self,_:&[&[u8]])->[u8;32]{panic!("hash outside summarized callee")}}
// Compare against the existing expected record without a second 896-byte
// symbolic shadow array or a harness input-copy loop.
fn fields(row:u8,payload:&[u8])->Result<(),Error>{RealR3_context::fields(row,payload)}
fn check<const N:usize,const PFX:usize>(row:u8){
 let initial:[u8;32]=kani::any();let next:u8=kani::any();let payload:[u8;N]=kani::any();let prefix:[u8;PFX]=kani::any();
  let x:[u32;4]=kani::any();let value=QM31{c0:field::CM31{a:field::M31(x[0]),b:field::M31(x[1])},c1:field::CM31{a:field::M31(x[2]),b:field::M31(x[3])}};
 // Independently constructed expected frame, not a call to wire::record.
 let (tag,size)=wire::row_shape(row).unwrap();assert_eq!(size,N);
 let mut frame=vec![tag];frame.extend_from_slice(&(N as u32).to_le_bytes());frame.extend_from_slice(&payload);
 RealR3_context::setup(frame,row,initial,next,value);
 if row==15 {RealR3_context::setup_fields();}
 let mut st=SemanticTranscript{state:initial,hash:NoHash,next_row:next};let mut bytes=prefix.to_vec();
 let a=native(row,&payload,&mut st,&mut bytes);let calls=RealR3_context::count_reset();let field_calls=RealR3_context::field_count_reset();
 let (b,after,out)=owned(row,payload.to_vec(),SemanticTranscript{state:initial,hash:NoHash,next_row:next},prefix.to_vec());
 assert_eq!(field_calls,RealR3_context::field_count_reset());assert_eq!(calls,RealR3_context::count_reset());assert!(calls<=1);
 assert_eq!(a,b);assert_eq!(st.state,after.state);assert_eq!(st.next_row,after.next_row);assert_eq!(bytes.len(),out.len());
 let j:usize=kani::any();kani::assume(j<bytes.len());assert_eq!(bytes[j],out[j]);
}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(89)] fn row03(){check::<0,79>(3)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(94)] fn row04(){check::<0,84>(4)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(99)] fn row05(){check::<0,89>(5)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(104)] fn row06(){check::<0,94>(6)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(109)] fn row07(){check::<0,99>(7)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(114)] fn row08(){check::<0,104>(8)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(119)] fn row09(){check::<0,109>(9)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(124)] fn row10(){check::<0,114>(10)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(129)] fn row11(){check::<0,119>(11)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(134)] fn row12(){check::<0,124>(12)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(139)] fn row13(){check::<0,129>(13)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::unwind(176)] fn row14(){check::<32,134>(14)}
#[kani::proof]
#[kani::stub(crate::wire::SemanticTranscript::semantic,crate::RealR3_context::native)]
#[kani::stub(crate::wire::semantic20::semantic,crate::RealR3_context::owned)]
#[kani::stub(crate::wire::validate_record_fields,fields)]
#[kani::unwind(1080)] fn row15(){check::<896,171>(15)}
}
