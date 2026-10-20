extern crate self as aspis_core;
pub mod field;
pub trait Digest32: Copy {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32];
}
pub mod sampler {use crate::field::{WideExact,CM31,M31,QM31};
fn low_base_p_digits(_: &[u8;32])->([u32;8],u32){unreachable!()}
fn add_small_base_p(_: &mut [u32;8],_:u32)->bool{unreachable!()}
fn decode8(digits: [u32; 8]) -> WideExact {
    WideExact::new(
        QM31 {
            c0: CM31::new(M31(digits[0]), M31(digits[1])),
            c1: CM31::new(M31(digits[2]), M31(digits[3])),
        },
        QM31 {
            c0: CM31::new(M31(digits[4]), M31(digits[5])),
            c1: CM31::new(M31(digits[6]), M31(digits[7])),
        },
    )
}
pub fn ordinary_sample(block: &[u8; 32]) -> WideExact {
    let (digits, _) = low_base_p_digits(block);
    decode8(digits)
}
pub fn gamma_sample(block: &[u8; 32]) -> WideExact {
    let (mut digits, quotient) = low_base_p_digits(block);
    let wrapped = add_small_base_p(&mut digits, quotient + 1);
    if wrapped {
        let wrapped_again = add_small_base_p(&mut digits, 1);
        debug_assert!(!wrapped_again);
    }
    decode8(digits)
}
}
pub mod trace {pub fn value(_:u16,_:usize,_:crate::field::WideExact){unreachable!()}}
pub mod transcript {use crate::{Digest32,field::WideExact as E};
pub struct Transcript<H: Digest32> { pub state:[u8;32], hash:H }
impl<H:Digest32> Transcript<H> {pub fn block(&mut self,_:u8,_:&[u8])->[u8;32]{unreachable!()}
pub fn scalar(&mut self,row:u8,payload:&[u8],nonzero:bool)->E {
        let block=self.block(row,payload);
        let out=if nonzero {crate::sampler::gamma_sample(&block)} else {crate::sampler::ordinary_sample(&block)};
        crate::trace::value(4,row as usize,out); out
    }
}}
