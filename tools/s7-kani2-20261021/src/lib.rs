#![allow(dead_code,unexpected_cfgs)]
#[cfg(kani)]
mod certificate {
use std::vec::Vec;
const P:u32=0x7fffffff;
#[derive(Clone,Copy,Debug,kani::Arbitrary)] struct M31(u32);
#[derive(Clone,Copy,Debug,kani::Arbitrary)] struct CM31{a:M31,b:M31}
#[derive(Clone,Copy,Debug,kani::Arbitrary)] struct K{c0:CM31,c1:CM31}
fn k_ok(k:K)->bool{k.c0.a.0<P && k.c0.b.0<P && k.c1.a.0<P && k.c1.b.0<P}
fn scalar_spec(raw:u64,limb:u32,basis:u32,flush:bool)->u64 {
 let v=raw+u64::from(limb)*u64::from(basis);
 if flush {(v&0x7fffffff)+(v>>31)} else {v}
}
fn row_equal(a:[u64;4],b:[u64;4])->bool{a[0]==b[0] && a[1]==b[1] && a[2]==b[2] && a[3]==b[3]}
fn row_safe(row:[u64;4],power:K,basis:M31)->bool {
 row[0]<=u64::MAX-u64::from(power.c0.a.0)*u64::from(basis.0) &&
 row[1]<=u64::MAX-u64::from(power.c0.b.0)*u64::from(basis.0) &&
 row[2]<=u64::MAX-u64::from(power.c1.a.0)*u64::from(basis.0) &&
 row[3]<=u64::MAX-u64::from(power.c1.b.0)*u64::from(basis.0)
}
fn row_spec(row:[u64;4],power:K,basis:M31,flush:bool)->[u64;4]{
 [scalar_spec(row[0],power.c0.a.0,basis.0,flush),scalar_spec(row[1],power.c0.b.0,basis.0,flush),scalar_spec(row[2],power.c1.a.0,basis.0,flush),scalar_spec(row[3],power.c1.b.0,basis.0,flush)]
}
include!("steps.rs");
mod vectors {include!("vectors.rs");}
}

#[cfg(kani)] mod field;
