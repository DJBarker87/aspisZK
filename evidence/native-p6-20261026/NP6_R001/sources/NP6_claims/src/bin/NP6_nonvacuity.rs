extern crate alloc;
#[path="../NP6_sampler.rs"]mod sampler;
#[path="../NP6_wire.rs"]mod r1_wire;
#[path="../NP6_shipped.rs"]mod shipped;
#[path="../NP6_reference.rs"]mod reference;
use aspis_core::field::{QM31,CM31,M31};
fn value(v:usize)->QM31{
 let a=11*v as u32+1;
 QM31{c0:CM31{a:M31(a),b:M31(a+1)},c1:CM31{a:M31(a+2),b:M31(a+3)}}
}
fn main(){
 let mut bytes=alloc::vec![0u8;32];
 for row in 0u8..27 {
  let size=r1_wire::row_shape(row).unwrap().1;
  let mut payload=alloc::vec![0u8;size];
  if row==25 {for v in 0..116 {payload[32*v..32*v+16].copy_from_slice(&value(v).to_le_bytes());}}
  bytes.extend_from_slice(&r1_wire::record(row,&payload).unwrap());
 }
 let prefix=r1_wire::Prefix::parse(&bytes).unwrap();
 let native=shipped::call(&prefix).unwrap();
 let owned=reference::call(&prefix).unwrap();
 assert!(native==owned);
 for p in 0..3 {for j in 0..29 {assert!(native[p][j]==value(29*p+j));}}
 println!("actual Prefix::parse accepted {} bytes; row25 is 3717 bytes; native/reference return all87 nonzero QM31 values identically",bytes.len());
}
