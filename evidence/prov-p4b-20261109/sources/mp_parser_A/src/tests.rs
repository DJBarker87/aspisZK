use super::{frozen as f,reference as r};
use aspis_core::Digest32;
#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {fn digest(&self,parts:&[&[u8]])->[u8;32] {
 let mut d=[0u8;32];for part in parts {for (i,b) in part.iter().enumerate(){d[i%32]=d[i%32].wrapping_mul(31).wrapping_add(*b);}}d
}}
#[test] fn whole_binary_level_recursion_matches_frozen(){
 for n in 1..=16 {for seed in 0..48u32 {
  let mut idx=[0u32;16];let mut val=[[0u8;32];16];
  for j in 0..n {idx[j]=(j as u32)*(1+seed%4)+seed;val[j]=[(j+1) as u8;32];}
  let nodes=vec![7u8;32*288];
  let s=r::Scratch{idx,val,n,at:0};let next=match r::levels(Hash,s,&nodes,18) {r::Level::Done(s)=>s,_=>panic!("sufficient nodes")};
  let count=f::multiproof::node_count(f::multiproof::Arity::Two,&idx[..n]).unwrap();
  let root=next.val[0];
  assert!(f::multiproof::verify_in_place(Hash,f::multiproof::Arity::Two,&root,&mut idx,&mut val,n,&nodes[..32*count]));
  assert_eq!((idx,val),(next.idx,next.val));assert_eq!(next.at,32*count);
 }}
}
#[test] fn compact_rows_offsets_and_suffix(){
 assert_eq!(r::semantic_offsets(0,32,32),Some((7015,13831)));
 for n in 0..64 {let bytes=vec![0;n];assert_eq!(f::compact::check_values(&bytes).is_ok(),r::check_values(&bytes));}
}

#[test] fn rejection_retains_partial_scratch() {
 for n in 1..=16 {for words in 0..20 {
  let mut idx=[0;16];let mut val=[[0;32];16];for j in 0..n {idx[j]=(3*j) as u32;val[j]=[(j+1) as u8;32];}
  let s=r::Scratch{idx,val,n,at:0};let nodes=vec![7;32*words];
  let old=f::multiproof::verify_in_place(Hash,f::multiproof::Arity::Two,&[0;32],&mut idx,&mut val,n,&nodes);
  let (new,out)=r::verify_owned(Hash,[0;32],s,&nodes);
  assert_eq!(old,new);assert_eq!((idx,val),(out.idx,out.val));
 }}
}
fn frozen_parse(bytes:&[u8])->Option<Vec<Vec<u8>>> {
 f::parser::parse_shape(bytes).ok()?;f::parser::canonical_scan(bytes).ok()?;
 let mut logical=vec![0;f::compact::LOGICAL_SEMANTIC];
 f::compact::expand_semantic(&bytes[16..7031],&mut logical).ok()?;
 let p=f::r1_wire::Prefix::parse(&logical).ok()?;
 Some((0..27).map(|r|p.record(r).unwrap().to_vec()).collect())
}
fn valid_stored()->Vec<u8> {
 let mut bytes=vec![0;57607];bytes[..8].copy_from_slice(b"R1P3CB18");bytes[8]=2;
 let mut at=48;
 for row in 0..27 {let (tag,size)=f::r1_wire::row_shape(row).unwrap();
 bytes[at]=tag;bytes[at+1..at+5].copy_from_slice(&(size as u32).to_le_bytes());
 at+=5+if row>=14 {size/2}else{size};}
 assert_eq!(at,7031);bytes
}
#[test] fn whole_parser_matches_exact_source_cuts(){
 let mut bytes=valid_stored();let expected=frozen_parse(&bytes);assert!(expected.is_some());
 assert_eq!(expected,super::parser_reference::parse(&bytes));
 // Mutations straddle framing, canonical fields, roots, salts and node slots.
 let positions=[0,7,8,9,15,16,47,48,49,52,58,60,7027,7030,7031,7494,7495,7526,7527,
 7750,7751,7782,7783,8006,8007,10054,10055,10662,10663,10726,10727,10854,10855,10886,28358,28359,57606];
 for at in positions {for byte in [1,127,128,255] {
 let old=bytes[at];bytes[at]=byte;assert_eq!(frozen_parse(&bytes),super::parser_reference::parse(&bytes),"at={at}");bytes[at]=old;
 }}
 for at in [7031,7495,7527,7783,8007,10055,10159,10535,10727] {
 let old=bytes[at..at+4].to_vec();bytes[at..at+4].copy_from_slice(&0x7fffffffu32.to_le_bytes());
 assert!(frozen_parse(&bytes).is_none());assert!(super::parser_reference::parse(&bytes).is_none());bytes[at..at+4].copy_from_slice(&old);
 }
 assert!(super::parser_reference::parse(&bytes[..57606]).is_none());
}
