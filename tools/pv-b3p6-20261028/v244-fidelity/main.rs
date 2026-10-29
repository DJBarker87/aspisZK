//! Finite changed-write observations; never a universal equality proof.
use aspis_core::field::{M31,CM31,QM31,P};
#[path="../v244/reference_field.rs"] mod reference_field;
mod reference_poseidon {
    include!("../v244/reference_poseidon.rs");
    pub fn observations(seed:u32,state:[QM31;16],constants:[u32;16]) {
        let mut external=state; external_linear_lazy(&mut external);
        assert_ne!(external,state); super::emit("external_linear_lazy",seed,&external);
        let mut internal=state; internal_linear_lazy(&mut internal);
        assert_ne!(internal,state); super::emit("internal_linear_lazy",seed,&internal);
        let full=full_round(state,core::array::from_fn(|i|super::q(constants[i])));
        assert_ne!(full,state); super::emit("full_round",seed,&full);
        let full_base=full_round_m31_constants(state,constants);
        assert_ne!(full_base,state); super::emit("full_round_m31_constants",seed,&full_base);
        super::emit("full_round_packed",seed,&full_round_packed(state,core::array::from_fn(|i|super::q(constants[i]))));
        super::emit("full_round_m31_constants_packed",seed,&full_round_m31_constants_packed(state,constants));
        let round=internal_round(state,super::q(seed+71));
        assert_ne!(round,state); super::emit("internal_round",seed,&round);
    }
}
fn q(n:u32)->QM31 {QM31{c0:CM31::new(M31(n%P),M31(n.wrapping_mul(17)%P)),c1:CM31::new(M31(n.wrapping_mul(31)%P),M31(n.wrapping_mul(47)%P))}}
fn emit(name:&str,seed:u32,values:&[QM31]) {
 let words:Vec<u32>=values.iter().flat_map(|x|[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]).collect();
 println!("{{\"function\":\"{name}\",\"seed\":{seed},\"limbs\":{words:?}}}");
}
fn main(){
 assert!(!cfg!(debug_assertions));
 for seed in [0u32,1,7,19] {
  let state=core::array::from_fn(|i|q((seed+1)*131+i as u32));
  let constants=core::array::from_fn(|i|((seed+1)*173+i as u32)%P);
  reference_poseidon::observations(seed,state,constants);
  let left=core::array::from_fn(|i|reference_field::PreparedQm31Multiplier::new(q((seed+1)*31+i as u32)));
  let right=core::array::from_fn(|i|q((seed+1)*43+i as u32));
  let prepared=reference_field::qm31_sum_products3_prepared(&left,&right);
  assert_ne!(prepared,QM31::ZERO);emit("qm31_sum_products3_prepared",seed,&[prepared]);
  let weights=core::array::from_fn(|i|q((seed+1)*59+i as u32));
  let values=core::array::from_fn(|i|M31((seed+1)*61+i as u32));
  let dot=reference_field::qm31_m31_dot(&weights,&values);
  assert_ne!(dot,QM31::ZERO);emit("qm31_m31_dot",seed,&[dot]);
 }
}
