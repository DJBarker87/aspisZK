// Each root covers an actual source helper, including ordinary rejection.
// All four independently checked field-codec contracts are installed.
macro_rules! codec_root {
 ($name:ident,$bound:literal,$body:block) => {
  #[kani::proof]
  #[kani::stub_verified(crate::decode_k_words)]
  #[kani::stub_verified(crate::decode_e_words)]
  #[kani::stub_verified(crate::encode_k)]
  #[kani::stub_verified(crate::encode_e_byte)]
  #[kani::stub(aspis_core::field::QM31::from_le_bytes,crate::decode_k)]
  #[kani::stub(aspis_core::field::WideExact::from_le_bytes,crate::decode_e)]
  #[kani::unwind($bound)]
  fn $name() $body
 };
}
codec_root!(raw_sections,34,{
 let b:[u8;1768]=kani::any();let at:usize=kani::any();kani::assume(at<=1736);
 let mut r=Reader{bytes:&b,at};let x=r.raw::<32>();
 let i:usize=kani::any();kani::assume(i<32);
 assert_eq!(x[i],b[at+i]);assert_eq!(r.at,at+32);
 assert!(core::ptr::eq(r.bytes,&b[..]));
});
codec_root!(wide_section,34,{
 let b:[u8;32]=kani::any();let mut r=Reader{bytes:&b,at:0};
 let got=r.e();let want=crate::decode_e_spec(&b).ok_or(Error::Checkpoint);
 assert_eq!(got,want);assert_eq!(r.at,32);assert!(core::ptr::eq(r.bytes,&b[..]));
});
codec_root!(qm31_section,18,{
 let b:[u8;16]=kani::any();let mut r=Reader{bytes:&b,at:0};
 let got=r.k();let want=crate::decode_k_spec(&b).ok_or(Error::Checkpoint);
 assert_eq!(got,want);assert_eq!(r.at,16);assert!(core::ptr::eq(r.bytes,&b[..]));
});
codec_root!(query_section,24,{
 let qs:[u32;22]=kani::any();let got=validate_checkpoint_queries(&qs);
 let mut valid=true;
 for i in 0..22 {if qs[i]>=262144 {valid=false;}for j in 0..i {if qs[i]==qs[j] {valid=false;}}}
 assert_eq!(got,if valid {Ok(())} else {Err(Error::Checkpoint)});
});
codec_root!(semantic_section,34,{
 let b:[u8;160]=kani::any();let got=read_checkpoint_semantic_alpha(&b,0);
 let mut expected=[K::ZERO;10];let mut valid=true;
 for i in 0..10 {match crate::decode_k_spec(&b[16*i..16*i+16]) {Some(x)=>expected[i]=x,None=>valid=false}}
 match got {Ok((values,at))=>{assert!(valid);assert_eq!(at,160);assert_eq!(values,expected)},Err(e)=>{assert!(!valid);assert_eq!(e,Error::Checkpoint)}}
});
codec_root!(weight_section,66,{
 let b:[u8;1024]=kani::any();let weights=vec![K::ZERO;64];
 let got=read_checkpoint_weights(&b,0,weights);
 let j:usize=kani::any();kani::assume(j<64);
 let mut valid=true;for i in 0..64 {if crate::decode_k_spec(&b[16*i..16*i+16]).is_none(){valid=false;}}
 match got {Ok((values,at))=>{assert!(valid);assert_eq!(at,1024);assert_eq!(values.len(),64);assert_eq!(Some(values[j]),crate::decode_k_spec(&b[16*j..16*j+16]))},Err(e)=>{assert!(!valid);assert_eq!(e,Error::Checkpoint)}}
});
