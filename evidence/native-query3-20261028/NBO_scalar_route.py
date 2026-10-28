from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
s+='''
static mut NBO_SCALAR_CALLS:usize=0;
static mut NBO_SCALAR_INPUT:[[u32;4];2]=[[0;4];2];
static mut NBO_SCALAR_SCALE:[u32;2]=[0;2];
static mut NBO_SCALAR_OUTPUT:[[u32;4];2]=[[0;4];2];
fn NBO_qwords(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn NBO_qfrom(w:[u32;4])->K {K{c0:aspis_core::field::CM31{a:M31(w[0]),b:M31(w[1])},c1:aspis_core::field::CM31{a:M31(w[2]),b:M31(w[3])}}}
fn NBO_qscalar_spec(x:K,s:M31)->K {
 let w=NBO_qwords(x);assert!(s.0<2147483647);assert!(w[0]<2147483647);assert!(w[1]<2147483647);assert!(w[2]<2147483647);assert!(w[3]<2147483647);
 let out:[u32;4]=kani::any();
 kani::assume(out[0]<2147483647);kani::assume(out[1]<2147483647);kani::assume(out[2]<2147483647);kani::assume(out[3]<2147483647);
 kani::assume(out[0]as u64==(w[0]as u64*s.0 as u64)%2147483647);
 kani::assume(out[1]as u64==(w[1]as u64*s.0 as u64)%2147483647);
 kani::assume(out[2]as u64==(w[2]as u64*s.0 as u64)%2147483647);
 kani::assume(out[3]as u64==(w[3]as u64*s.0 as u64)%2147483647);
 unsafe{let i=NBO_SCALAR_CALLS;assert!(i<2);NBO_SCALAR_CALLS+=1;NBO_SCALAR_INPUT[i]=w;NBO_SCALAR_SCALE[i]=s.0;NBO_SCALAR_OUTPUT[i]=out;}
 NBO_qfrom(out)
}
#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::QM31::mul_m31,NBO_qscalar_spec)]
fn NBO_wide_scalar_dispatch(){
 let x=NBO_any_e();let scalar:u32=kani::any();kani::assume(scalar<2147483647);let k:usize=kani::any();kani::assume(k<8);
 let y=x.mul_m31(M31(scalar));
 unsafe{assert_eq!(NBO_SCALAR_CALLS,2);assert_eq!(NBO_SCALAR_INPUT[k/4][k%4],x.to_limbs()[k]);assert_eq!(NBO_SCALAR_SCALE[k/4],scalar);assert_eq!(y.to_limbs()[k],NBO_SCALAR_OUTPUT[k/4][k%4]);}
 kani::cover!(k==0);kani::cover!(k==7);kani::cover!(scalar==0);kani::cover!(scalar==2147483646);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
