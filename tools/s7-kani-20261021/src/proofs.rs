//! Symbolic correspondence. No arithmetic stubs and no assumed equivalences.
use super::*;
use support::*;
fn m31()->M31 {let x:u32=kani::any();kani::assume(x<0x7fffffff);M31(x)}
fn qm31()->K {use aspis_core::field::CM31;K{c0:CM31{a:m31(),b:m31()},c1:CM31{a:m31(),b:m31()}}}
fn wide()->E {E::new(qm31(),qm31())}
#[kani::proof]
#[kani::unwind(6)]
fn residue_row_correspondence() {
 let power=qm31();let basis=m31();let flush:bool=kani::any();let phase:u64=kani::any();kani::assume(phase<4);
 let row:[u64;4]=kani::any();
 let bound=(1u64<<34)+phase*2147483646u64*2147483646u64;
 for limb in row {kani::assume(limb<=bound);}
 let mut shipped=row;update_residue_row(&mut shipped,power,basis,flush);
 assert_eq!(shipped,residue_owned(row,power,basis,flush));
}
#[kani::proof]
#[kani::unwind(70)]
fn accumulate_real_width_correspondence() {
 let node=m31();let mut p=prepared([0;22]);p.rho=qm31();
 let next:usize=kani::any();kani::assume(next<22);
 let terms:usize=kani::any();kani::assume(terms<12);
 let raw:[u64;4]=kani::any();for limb in raw {kani::assume(limb<(1u64<<34));}
 let a=Accumulator{weights:alloc::vec![K::ZERO;64],rhs:wide(),power:qm31(),next};
 let b=BatchedWeights{raw:alloc::vec![raw;64],terms};let value=wide();
 let mut s=copy_a(&a);let mut t=copy_b(&b);accumulate_batched_with_node(&p,&mut s,node,value,&mut t);
 let (u,v)=accumulate_owned(p.rho,a,node,value,b);same(&s,&u,&t,&v);
}
#[kani::proof]
#[kani::unwind(24)]
fn geometry_query_offset_correspondence() {
 let start:usize=kani::any();let end:usize=kani::any();let i:usize=kani::any();
 kani::assume(start<=i && i<end && end<=22);
 let entries:[[u32;5];22]=kani::any();
 let mut inverses=Vec::new();for row in entries {inverses.push(row.map(M31));}
 let geometry=QueryGeometry{start,inverses,line_z:alloc::vec![M31::ONE;22]};
 assert_eq!(*geometry.for_query(i),entries[i-start].map(M31));
 assert!(5*(i-start)+4<5*(end-start));
}

// The Lean phase_bound theorem discharges these exact preconditions for real
// canonical limbs and the four-query retained-residue invariant.
#[kani::proof]
#[kani::unwind(6)]
fn row_correspondence_under_checked_products() {
 let power=qm31();let basis=m31();let flush:bool=kani::any();
 let row:[u64;4]=kani::any();
 let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
 for j in 0..4 {let product=u64::from(limbs[j])*u64::from(basis.0);kani::assume(row[j]<=u64::MAX-product);}
 let mut shipped=row;update_residue_row(&mut shipped,power,basis,flush);
 assert_eq!(shipped,residue_owned(row,power,basis,flush));
}

#[kani::proof]
#[kani::unwind(70)]
fn accumulate_first_query_real_width() {
 let node=m31();let p=prepared([0;22]);
 let a=Accumulator{weights:alloc::vec![K::ZERO;64],rhs:E::ZERO,power:K::ONE,next:0};
 let b=BatchedWeights{raw:alloc::vec![[0;4];64],terms:0};
 let mut s=copy_a(&a);let mut t=copy_b(&b);accumulate_batched_with_node(&p,&mut s,node,E::ZERO,&mut t);
 let (u,v)=accumulate_owned(p.rho,a,node,E::ZERO,b);same(&s,&u,&t,&v);
}
