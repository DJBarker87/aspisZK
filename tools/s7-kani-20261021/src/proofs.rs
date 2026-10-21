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
 let owned=residue_owned(row,power,basis,flush);
 for j in 0..4 {assert_eq!(shipped[j],owned[j]);}
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
 let owned=residue_owned(row,power,basis,flush);
 for j in 0..4 {assert_eq!(shipped[j],owned[j]);}
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

fn one_lane(lane:usize) {
 use aspis_core::field::CM31;
 let limb=m31();let basis=m31();let old:u64=kani::any();let flush:bool=kani::any();
 let product=u64::from(limb.0)*u64::from(basis.0);
 kani::assume(old<=u64::MAX-product);
 let mut limbs=[M31::ZERO;4];limbs[lane]=limb;
 let power=K{c0:CM31{a:limbs[0],b:limbs[1]},c1:CM31{a:limbs[2],b:limbs[3]}};
 let mut row=[0u64;4];row[lane]=old;
 let mut shipped=row;update_residue_row(&mut shipped,power,basis,flush);
 let owned=residue_owned(row,power,basis,flush);
 for j in 0..4 {assert_eq!(shipped[j],owned[j]);}
}
#[kani::proof] #[kani::unwind(6)] fn scalar_lane0(){one_lane(0);}
#[kani::proof] #[kani::unwind(6)] fn scalar_lane1(){one_lane(1);}
#[kani::proof] #[kani::unwind(6)] fn scalar_lane2(){one_lane(2);}
#[kani::proof] #[kani::unwind(6)] fn scalar_lane3(){one_lane(3);}

// Each source fragment is lifted literally by generate.py from the frozen
// loop. Other lanes are arbitrary and frame preservation is asserted.
fn fragment_lane(j:usize) {
 let power=qm31();let basis=m31();let raw:[u64;4]=kani::any();let flush:bool=kani::any();
 let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
 let product=u64::from(limbs[j])*u64::from(basis.0);
 kani::assume(raw[j]<=u64::MAX-product);
 let mut row=raw;frozen_update_limb(&mut row,power,basis,j);
 if flush {frozen_fold_limb(&mut row[j]);}
 let expected=residue_scalar_owned(raw[j],limbs[j],basis.0,flush);
 assert_eq!(row[j],expected);
 for k in 0..4 {if k!=j {assert_eq!(row[k],raw[k]);}}
}
#[kani::proof] #[kani::unwind(6)] fn fragment_lane0(){fragment_lane(0);}
#[kani::proof] #[kani::unwind(6)] fn fragment_lane1(){fragment_lane(1);}
#[kani::proof] #[kani::unwind(6)] fn fragment_lane2(){fragment_lane(2);}
#[kani::proof] #[kani::unwind(6)] fn fragment_lane3(){fragment_lane(3);}

#[kani::proof]
#[kani::unwind(112)]
fn grouping_step_correspondence() {
 let values:[u32;110]=kani::any();
 let mut inverse=Vec::new();for value in values {inverse.push(M31(value));}
 let i:usize=kani::any();kani::assume(i<22);
 let expected=frozen_group(&inverse,i);
 let grouped=groups_owned(inverse,Vec::new(),i,i+1);
 assert_eq!(grouped.len(),1);
 for j in 0..5 {assert_eq!(grouped[0][j],expected[j]);}
}

fn grouping_fixed_ordinal(i:usize) {
 let values:[u32;110]=kani::any();let mut inverse=Vec::new();for value in values {inverse.push(M31(value));}
 let expected=frozen_group(&inverse,i);let grouped=groups_owned(inverse,Vec::new(),i,i+1);
 assert_eq!(grouped.len(),1);for j in 0..5 {assert_eq!(grouped[0][j],expected[j]);}
}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_0(){grouping_fixed_ordinal(0);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_1(){grouping_fixed_ordinal(1);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_2(){grouping_fixed_ordinal(2);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_3(){grouping_fixed_ordinal(3);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_4(){grouping_fixed_ordinal(4);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_5(){grouping_fixed_ordinal(5);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_6(){grouping_fixed_ordinal(6);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_7(){grouping_fixed_ordinal(7);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_8(){grouping_fixed_ordinal(8);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_9(){grouping_fixed_ordinal(9);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_10(){grouping_fixed_ordinal(10);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_11(){grouping_fixed_ordinal(11);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_12(){grouping_fixed_ordinal(12);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_13(){grouping_fixed_ordinal(13);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_14(){grouping_fixed_ordinal(14);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_15(){grouping_fixed_ordinal(15);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_16(){grouping_fixed_ordinal(16);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_17(){grouping_fixed_ordinal(17);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_18(){grouping_fixed_ordinal(18);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_19(){grouping_fixed_ordinal(19);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_20(){grouping_fixed_ordinal(20);}
#[kani::proof] #[kani::unwind(112)] fn grouping_ordinal_21(){grouping_fixed_ordinal(21);}
