#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K,CM31,M31};
fn bytes<const N:usize>(seed:usize)->[u8;N]{core::array::from_fn(|j|((j*37+seed*19)%256) as u8)}
fn witness(actual:u8,correct:u8){assert_eq!(actual,correct);assert_ne!(actual,correct^1);}
fn append<const N:usize>(len:usize){let initial=bytes::<1736>(len);let source=bytes::<N>(7);let mut out=KMX_stubs::KMX_to_vec(&initial[..len]);assert_eq!(out.capacity(),len);KMX_stubs::KMX_extend_from_slice(&mut out,&source);assert_eq!(out.len(),len+N);assert_eq!(&out[..len],&initial[..len]);assert_eq!(&out[len..],&source);witness(out[len],source[0]);}
fn main(){let case=std::env::args().nth(1).unwrap();match case.as_str(){
 "query"=>{for i in (1..16).chain(17..22){let len=64+4*i;let source=bytes::<4>(i);let mut out=if i<16{Vec::from(bytes::<128>(i))}else{Vec::from(bytes::<256>(i))};let initial=out.clone();let cap=out.capacity();out.truncate(len);KMX_stubs::KMX_extend_from_slice(&mut out,&source);assert_eq!(out.capacity(),cap);assert_eq!(out.len(),len+4);assert_eq!(&out[..len],&initial[..len]);assert_eq!(&out[len..],&source);witness(out[0],initial[0]);witness(out[len],source[0]);}},
 "body"=>{let initial=bytes::<1736>(3);let source=bytes::<32>(4);let mut out=Vec::from(initial);KMX_stubs::KMX_extend_from_slice(&mut out,&source);assert_eq!(out.len(),1768);assert_eq!(out.capacity(),3472);assert_eq!(&out[..1736],&initial);assert_eq!(&out[1736..],&source);for j in 0..1768{witness(out[j],if j<1736{initial[j]}else{source[j-1736]});}
 unsafe{let old=alloc::alloc::Layout::array::<u8>(1736).unwrap();let p=alloc::alloc::alloc(old);assert!(!p.is_null());for j in 0..1736{p.add(j).write(initial[j]);}let p=KMX_stubs::KMX_realloc(p,old,3472);assert!(!p.is_null());for j in 0..1736{witness(p.add(j).read(),initial[j]);}alloc::alloc::dealloc(p,alloc::alloc::Layout::array::<u8>(3472).unwrap());}},
 "selected"=>{for i in 0..64{let raw=[i as u32,0x12345678,0xffffffff,0];let selected=K{c0:CM31{a:M31(raw[0]),b:M31(raw[1])},c1:CM31{a:M31(raw[2]),b:M31(raw[3])}};let shared=&selected;let &x=shared;let len=712+16*i;let initial=bytes::<1736>(i);let mut out=KMX_stubs::KMX_to_vec(&initial[..len]);let mut b=[0;16];x.write_le_bytes(&mut b);KMX_stubs::KMX_extend_from_slice(&mut out,&b);assert_eq!(&out[..len],&initial[..len]);assert_eq!(out.len(),len+16);for j in 0..16{witness(out[len+j],raw[j/4].to_le_bytes()[j%4]);}}},
 "append16"=>{for len in 0..=1720{append::<16>(len);}},
 "append32and4"=>{for len in 0..=1704{append::<32>(len);}for len in 0..=1732{append::<4>(len);let word=(len as u32).wrapping_mul(0x1234567);let mut out=KMX_stubs::KMX_to_vec(&bytes::<1736>(len)[..len]);KMX_stubs::KMX_extend_from_slice(&mut out,&word.to_le_bytes());for k in 0..4{witness(out[len+k],((word>>(8*k))&255) as u8);}}},
 _=>panic!("unknown case")};println!("KNA_NATIVE_PASS {}: correct equality holds and XOR1 control equality fails",case);}
