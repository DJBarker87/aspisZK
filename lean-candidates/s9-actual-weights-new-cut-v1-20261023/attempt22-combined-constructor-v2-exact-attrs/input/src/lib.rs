#![no_std]
extern crate alloc;
extern crate self as aspis_core;

pub mod field;
pub mod circle;
pub mod state_only_prefix;

use alloc::boxed::Box;
use circle::SecureCirclePoint;
use field::QM31 as K;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Variant { S1, S2, D }
const TAU: [usize; 5] = [3, 4, 2, 0, 1];
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error { Allocation }

#[inline(always)]
fn double(x: K) -> K { x.mul(x).add(x.mul(x)).sub(K::ONE) }

pub struct Weights {
    pub variant: Variant,
    pub factors: [[[K; 4]; 5]; 5],
    pub points: [[K; 10]; 3],
    pub extra: [K; 2],
}

/// Root-only extraction wrapper. The body is copied from the pinned v2 Weights::new method.
#[inline(never)]
pub fn weights_new(variant: Variant, alpha: &[K; 10], z: &[SecureCirclePoint; 2]) -> Result<Box<Weights>, Error> {
        let points=aspis_core::state_only_prefix::r0::statement_points(alpha);
        let extra=[alpha[8],alpha[9]];
        let mut factors=[[[K::ZERO;4];5];5];
        for k in 0..3 { for d in 0..5 {
            let a=points[k][9-2*TAU[d]]; let b=points[k][8-2*TAU[d]];
            factors[k][d]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
        }}
        for k in 0..2 {
            factors[3+k][0]=[K::ONE,z[k].y,z[k].x,z[k].x.mul(z[k].y)];
            let mut x=double(z[k].x);
            for d in 1..5 {
                let y=double(x); factors[3+k][d]=[K::ONE,x,y,x.mul(y)]; x=double(y);
            }
        }
        Ok(Weights::box_from_parts(variant, factors, points, extra))
}

impl Weights {
    #[inline(never)]
    fn box_from_parts(variant:Variant,factors:[[[K;4];5];5],points:[[K;10];3],extra:[K;2])->Box<Self> {
            Box::new(Self { variant, factors, points, extra })
        }
}
