use super::equivalence16::{q,qs};
use aspis_core::field::{QM31,M31};
use aspis_statement::state_only_poseidon::StateOnlyPoseidonOpenings;
use crate::{host_terminal::remaining16 as d,reference_terminal::remaining16 as r};
fn openings()->StateOnlyPoseidonOpenings {StateOnlyPoseidonOpenings{z:qs(),succ_z:qs(),xor12_z:qs()}}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn validate_transition() {let p=crate::inputs16::public();assert_eq!(d::validate(p),r::validate(p));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn poseidon_selectors() {let h=qs();let l=qs();assert_eq!(d::poseidon(h,l),r::poseidon(h,l));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn path_lanes_literal() {let v=q();let o=openings();assert_eq!(d::path(v,&o),r::path(v,&o));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn semantic_initial_and_absorption() {let p=crate::inputs16::public();let o=openings();let h=qs();let l=qs();assert_eq!(d::initial(p,&o,h,l),r::initial(p,&o,h,l));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn public_digest_lanes() {let p=crate::inputs16::public();let o=openings();let h=qs();let l=qs();assert_eq!(d::digests(p,&o,h,l),r::digests(p,&o,h,l));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn semantic_packed() {let p=crate::inputs16::public();let o=openings();let h=qs();let l=qs();assert_eq!(d::semantic(p,&o,h,l),r::semantic(p,&o,h,l));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn composition_parts() {let p=crate::inputs16::public();let c=qs();let point=qs();let a=qs();assert_eq!(d::composition(p,&c,&point,a),r::composition(p,&c,&point,a));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn add_path_lanes() {let mut a=qs();let mut b=a;let o=openings();let h=qs();let l=qs();d::add_path_lanes(&mut a,&o,h,l);r::add_path_lanes(&mut b,&o,h,l);assert_eq!(a,b);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn add_value_lanes() {let mut a=qs();let mut b=a;let o=openings();let h=qs();let l=qs();d::add_value_lanes(&mut a,&o,h,l);r::add_value_lanes(&mut b,&o,h,l);assert_eq!(a,b);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn add_schedule_lanes() {let mut a=qs();let mut b=a;let o=openings();let h=qs();let l=qs();let p=crate::inputs16::public();d::add_schedule_lanes(&mut a,p,&o,h,l);r::add_schedule_lanes(&mut b,p,&o,h,l);assert_eq!(a,b);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn absorption_lanes_literal() {let a=qs();let v=qs();assert_eq!(crate::host_terminal::access16::absorption(a,&v),crate::reference_terminal::access16::absorption(a,&v));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn occupancy_lanes_literal() {let a=q();let b=q();let c=M31(kani::any());let v=qs();assert_eq!(crate::host_terminal::access16::occupancy(a,b,c,&v),crate::reference_terminal::access16::occupancy(a,b,c,&v));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn active_literal() {let h=qs();let l=qs();assert_eq!(crate::host_copy_terminal::access16::active(h,l),crate::reference_copy_terminal::access16::active(h,l));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn pattern_values_literal() {let v=qs();let l=q();assert_eq!(crate::host_copy_terminal::access16::pattern(&v,l),crate::reference_copy_terminal::access16::pattern(&v,l));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn interpolated_internal_pair() {let s=qs();let l=qs();assert_eq!(crate::deployed_poseidon16::access16::pair(s,&l),crate::reference_poseidon16::access16::pair(s,&l));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn interpolate_three_constant_columns() {let w=qs();let a=kani::any();let b=kani::any();let c=kani::any();assert_eq!(crate::deployed_poseidon16::access16::interpolate(w,a,b,c),crate::reference_poseidon16::access16::interpolate(w,a,b,c));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn leading_pair_packed() {let z=qs();let s=qs();let x=qs();assert_eq!(crate::deployed_poseidon16::access16::leading(z,s,x),crate::reference_poseidon16::access16::leading(z,s,x));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn evaluate_state_only_poseidon_oracle_projected() {let z=qs();let s=qs();let x=qs();let b=q();let l=qs();assert_eq!(crate::deployed_poseidon16::access16::projected(z,s,x,b,l),crate::reference_poseidon16::access16::projected(z,s,x,b,l));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn expand() {let p=qs();assert_eq!(crate::deployed_poseidon16::access16::expand_high(&p),crate::reference_copy_terminal::remaining16::expand_high(&p));assert_eq!(crate::deployed_poseidon16::access16::expand_low(&p),crate::reference_copy_terminal::remaining16::expand_low(&p));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn at_point_legacy49_refuted() {let p=qs();let (h,l)=crate::reference_copy_terminal::remaining16::at_point(&p);let r=crate::reference_terminal::remaining16::poseidon(h,l);assert_eq!(crate::deployed_poseidon16::access16::at_point(&p),(r.block,r.local));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn qm31_m31_dot() {let w=qs::<7>();let v:[u32;7]=kani::any();let mut m=[M31(0);7];let mut i=0;while i<7 {m[i]=M31(v[i]);i+=1;}assert_eq!(aspis_core::field::qm31_m31_dot(&w,&m),crate::reference_field::qm31_m31_dot(&w,&m));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn qm31_sum_products3_prepared() {let w=qs::<3>();let r=qs::<3>();let d=[aspis_core::field::PreparedQm31Multiplier::new(w[0]),aspis_core::field::PreparedQm31Multiplier::new(w[1]),aspis_core::field::PreparedQm31Multiplier::new(w[2])];let f=[crate::reference_field::PreparedQm31Multiplier::new(w[0]),crate::reference_field::PreparedQm31Multiplier::new(w[1]),crate::reference_field::PreparedQm31Multiplier::new(w[2])];assert_eq!(aspis_core::field::qm31_sum_products3_prepared(&d,&r),crate::reference_field::qm31_sum_products3_prepared(&f,&r));}
