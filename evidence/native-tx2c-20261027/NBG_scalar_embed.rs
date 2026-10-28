#[kani::proof]
fn NBG_scalar_embedding(){
 use crate::r0::scalar::CodeField;
 let raw:u32=kani::any();let out=<super::WideExact as CodeField>::from_m31(super::M31(raw));
 assert!(out.c0().c0.a.0==raw%super::P);
 assert!(out.c0().c0.b.0==0&&out.c0().c1.a.0==0&&out.c0().c1.b.0==0);
 assert!(out.c1().c0.a.0==0&&out.c1().c0.b.0==0&&out.c1().c1.a.0==0&&out.c1().c1.b.0==0);
 kani::cover!(raw==u32::MAX);
}
