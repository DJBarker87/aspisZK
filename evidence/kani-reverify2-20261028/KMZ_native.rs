#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K, WideExact as E};
fn witness(gate:&str,actual:u8,correct:u8){
 assert_eq!(actual,correct);assert_ne!(actual^1,correct);
 println!("{{\"gate\":\"{}\",\"source\":\"all zero\",\"prefix\":\"all zero\",\"selected_byte\":0,\"actual\":{},\"correct\":{},\"wrong_asserted_byte\":{}}}",gate,actual,correct,actual^1);
}
fn main(){match std::env::args().nth(1).unwrap().as_str(){
 "expand"=>{let src=[0u8;16];let mut dst=[0u8;96];KMX_stubs::KMX_copy_from_slice(&mut dst[..16],&src);witness("KMZ_K002",dst[0],0);},
 "local"=>{let src=[0u8;32];let mut dst=[0u8;64];KMX_stubs::KMX_copy_from_slice(&mut dst[..32],&src);witness("KMZ_K003",dst[0],0);},
 "wide"=>{let src=E::ZERO.to_le_bytes();let mut dst=[0u8;64];KMX_stubs::KMX_copy_from_slice(&mut dst[..32],&src);witness("KMZ_K004",dst[0],0);
 for (gate,len,cap) in [("KMZ_K007",0,0),("KMZ_K008",32,32),("KMZ_K029",64,64),("KMZ_K010",96,128),("KMZ_K030/031",128,128),("KMZ_K012",160,256)]{let initial=[0u8;160];let mut out=alloc::vec::Vec::with_capacity(cap);KMX_stubs::KMX_extend_from_slice(&mut out,&initial[..len]);KMX_stubs::KMX_extend_from_slice(&mut out,&src);assert_eq!(out.len(),len+32);witness(gate,out[0],0);witness(gate,out[len],0);}
 let mut out=alloc::vec::Vec::new();for (i,cap) in [32,64,128,128,256,256].into_iter().enumerate(){KMX_stubs::KMX_extend_from_slice(&mut out,&src);assert_eq!(out.capacity(),cap);assert_eq!(out.len(),32*(i+1));if i==0{assert_ne!(out.capacity(),33);println!("capacity32 actual=32 wrong=33");}}},
 "limb"=>{let src=0u32.to_le_bytes();let mut dst=[0u8;32];KMX_stubs::KMX_copy_from_slice(&mut dst[..4],&src);witness("KMZ_K005",dst[0],0);},
 "scalar"=>{let mut src=[0u8;16];K::ZERO.write_le_bytes(&mut src);let mut dst=[0u8;48];KMX_stubs::KMX_copy_from_slice(&mut dst[..16],&src);witness("KMZ_K006",dst[0],0);
 for i in 0..14{let len=16*i;let cap=[0,16,32,64,64,128,128,128,128,256,256,256,256,256][i];let initial=[0u8;208];let mut out=alloc::vec::Vec::with_capacity(cap);KMX_stubs::KMX_extend_from_slice(&mut out,&initial[..len]);KMX_stubs::KMX_extend_from_slice(&mut out,&src);assert_eq!(out.len(),len+16);witness(&format!("scalar_stage{}",i),out[0],0);}
 let mut out=alloc::vec::Vec::new();for (i,cap) in [16,32,64,64,128,128,128,128,256,256,256,256,256,256].into_iter().enumerate(){KMX_stubs::KMX_extend_from_slice(&mut out,&src);assert_eq!(out.capacity(),cap);assert_eq!(out.len(),16*(i+1));if i==0{assert_ne!(out.capacity(),17);println!("capacity16 actual=16 wrong=17");}}},
 _=>panic!("unknown witness")}}
