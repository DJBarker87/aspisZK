use aspis_core::field::{QM31,CM31,M31};
use super::equivalence16::{q,qs};
use crate::{host_terminal::remaining16 as d,reference_terminal::remaining16 as r};
use crate::{deployed_poseidon16::access16 as dp,reference_poseidon16::access16 as rp};
fn openings()->aspis_statement::state_only_poseidon::StateOnlyPoseidonOpenings {aspis_statement::state_only_poseidon::StateOnlyPoseidonOpenings{z:qs(),succ_z:qs(),xor12_z:qs()}}
fn lane(n:usize)->usize {let i:usize=kani::any();kani::assume(i<n);i}
fn component(q:QM31,n:usize)->u32 {match n {0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn sum_high_zero_57() {let h=qs();let l=qs();let ranges=[0..57];assert_eq!(crate::host_terminal::access16::sum(h,l,&ranges),crate::reference_terminal::access16::sum(h,l,&ranges));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn sum_high_nodes() {let h=qs();let l=qs();let ranges=[4..25,33..57];assert_eq!(crate::host_terminal::access16::sum(h,l,&ranges),crate::reference_terminal::access16::sum(h,l,&ranges));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn sum_high_path() {let h=qs();let l=qs();let ranges=[57..63];assert_eq!(crate::host_terminal::access16::sum(h,l,&ranges),crate::reference_terminal::access16::sum(h,l,&ranges));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn equality_component_0() {let a=qs();let b=qs();assert_eq!(component(crate::host_terminal::access16::equality(&a,&b),0),component(crate::reference_terminal::access16::equality(&a,&b),0));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn equality_component_1() {let a=qs();let b=qs();assert_eq!(component(crate::host_terminal::access16::equality(&a,&b),1),component(crate::reference_terminal::access16::equality(&a,&b),1));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn equality_component_2() {let a=qs();let b=qs();assert_eq!(component(crate::host_terminal::access16::equality(&a,&b),2),component(crate::reference_terminal::access16::equality(&a,&b),2));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn equality_component_3() {let a=qs();let b=qs();assert_eq!(component(crate::host_terminal::access16::equality(&a,&b),3),component(crate::reference_terminal::access16::equality(&a,&b),3));}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn path_half_0() {let v=q();let o=openings();let k=lane(17);assert_eq!(d::path(v,&o)[k].c0,r::path(v,&o)[k].c0);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn occupancy_half_0() {let a=q();let b=q();let c=M31(kani::any());let v=qs();let k=lane(12);assert_eq!(crate::host_terminal::access16::occupancy(a,b,c,&v)[k].c0,crate::reference_terminal::access16::occupancy(a,b,c,&v)[k].c0);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn internal_pair_half_0() {let s=qs();let l=qs();let k=lane(16);assert_eq!(dp::pair(s,&l)[k].c0,rp::pair(s,&l)[k].c0);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn leading_half_0() {let z=qs();let s=qs();let x=qs();let k=lane(4);assert_eq!(dp::leading(z,s,x)[k].c0,rp::leading(z,s,x)[k].c0);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn path_half_1() {let v=q();let o=openings();let k=lane(17);assert_eq!(d::path(v,&o)[k].c1,r::path(v,&o)[k].c1);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn occupancy_half_1() {let a=q();let b=q();let c=M31(kani::any());let v=qs();let k=lane(12);assert_eq!(crate::host_terminal::access16::occupancy(a,b,c,&v)[k].c1,crate::reference_terminal::access16::occupancy(a,b,c,&v)[k].c1);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn internal_pair_half_1() {let s=qs();let l=qs();let k=lane(16);assert_eq!(dp::pair(s,&l)[k].c1,rp::pair(s,&l)[k].c1);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn leading_half_1() {let z=qs();let s=qs();let x=qs();let k=lane(4);assert_eq!(dp::leading(z,s,x)[k].c1,rp::leading(z,s,x)[k].c1);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn round_index() {let s=qs();let c=qs();let k=lane(16);assert_eq!(dp::round(s,c)[k],rp::round(s,c)[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn round_m31_index() {let s=qs();let c=kani::any();let k=lane(16);assert_eq!(dp::round_m31(s,c)[k],rp::round_m31(s,c)[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn round_m31_packed_index() {let s=qs();let c=kani::any();let k=lane(4);assert_eq!(dp::round_m31_packed(s,c)[k],rp::round_m31_packed(s,c)[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn round_packed_index() {let s=qs();let c=qs();let k=lane(4);assert_eq!(dp::round_packed(s,c)[k],rp::round_packed(s,c)[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn interpolate_index() {let w=qs();let a=kani::any();let b=kani::any();let c=kani::any();let k=lane(16);assert_eq!(dp::interpolate(w,a,b,c)[k],rp::interpolate(w,a,b,c)[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn poseidon_selectors_index() {let h=qs();let l=qs();let k=lane(16);let a=d::poseidon(h,l);let b=r::poseidon(h,l);assert_eq!(a.block,b.block);assert_eq!(a.local[k],b.local[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn add_path_lanes_index() {let mut a=qs();let mut b=a;let o=openings();let h=qs();let l=qs();d::add_path_lanes(&mut a,&o,h,l);r::add_path_lanes(&mut b,&o,h,l);let k=lane(24);assert_eq!(a[k],b[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn add_value_lanes_index() {let mut a=qs();let mut b=a;let o=openings();let h=qs();let l=qs();d::add_value_lanes(&mut a,&o,h,l);r::add_value_lanes(&mut b,&o,h,l);let k=lane(24);assert_eq!(a[k],b[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn add_schedule_lanes_index() {let mut a=qs();let mut b=a;let o=openings();let h=qs();let l=qs();let p=crate::inputs16::public();d::add_schedule_lanes(&mut a,p,&o,h,l);r::add_schedule_lanes(&mut b,p,&o,h,l);let k=lane(24);assert_eq!(a[k],b[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn semantic_index() {let p=crate::inputs16::public();let o=openings();let h=qs();let l=qs();let k=lane(24);assert_eq!(d::semantic(p,&o,h,l)[k],r::semantic(p,&o,h,l)[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn initial_index() {let p=crate::inputs16::public();let o=openings();let h=qs();let l=qs();let k=lane(16);let a=d::initial(p,&o,h,l);let b=r::initial(p,&o,h,l);if kani::any(){assert_eq!(a.0[k],b.0[k]);}else{assert_eq!(a.1[k],b.1[k]);}}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn digest_index() {let p=crate::inputs16::public();let o=openings();let h=qs();let l=qs();let k=lane(8);assert_eq!(d::digests(p,&o,h,l)[k],r::digests(p,&o,h,l)[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn external_index() {let s=qs();let k=lane(16);assert_eq!(dp::external(s)[k],rp::external(s)[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn packed_index() {let s=qs();let k=lane(4);assert_eq!(dp::packed(s)[k],rp::packed(s)[k]);}
#[kani::proof] #[kani::unwind(256)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn projected_index() {let z=qs();let s=qs();let x=qs();let b=q();let l=qs();let k=lane(4);assert_eq!(dp::projected(z,s,x,b,l)[k],rp::projected(z,s,x,b,l)[k]);}
