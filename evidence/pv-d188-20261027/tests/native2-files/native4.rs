extern crate self as aspis_core;pub mod field;pub mod circle{use crate::field::QM31;#[derive(Clone,Copy)]pub struct SecureCirclePoint {
    pub x: QM31,
    pub y: QM31,
}}
mod weights{include!("op252.rs");}
mod public{include!("op226.rs");}
use field::{QM31,CM31,M31};
fn main(){
 let p=public::Public{withdrawal:false,anchor:[1;8],nullifier:[2;8],asset_id:3,recipient:[4;8],change:[5;8],withdrawal_amount:6,next_pair_index:7,frontier:[[8;8];20],next_root:[9;8],next_frontier:[[10;8];20]};
 match public::public_bytes(p){Ok((v,n))=>println!("public {:?} {}",v,n),Err(_)=>println!("public error")};
 let q=QM31{c0:CM31{a:M31(2),b:M31(0)},c1:CM31{a:M31(0),b:M31(0)}};
 let x=QM31{c0:CM31{a:M31(3),b:M31(0)},c1:q.c1};let y=QM31{c0:CM31{a:M31(4),b:M31(0)},c1:q.c1};
 match weights::weights_new(weights::Variant::D,&[q;10],&[circle::SecureCirclePoint{x,y};2]){Ok(w)=>println!("weights {:?}",w.factors.into_iter().flat_map(|a|a.into_iter().flat_map(|a|a.into_iter().map(|q|q.c0.a.0))).collect::<Vec<_>>()),Err(_)=>println!("weights error")};
}
