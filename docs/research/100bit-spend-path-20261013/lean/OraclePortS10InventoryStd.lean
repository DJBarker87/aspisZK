import OraclePortStdAllocation

/-! Forty affected declaration labels from the frozen compiler inventory.
This list is not the complete source driver and is not model_S10Join. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10InventoryStd
open OraclePortJoinSplitStd

def inventory : List Site := [
  ⟨.owned .s3, "aspis_r1_cost_probe::weights::powers"⟩,
  ⟨.owned .s5, "aspis_core::field::wide_exact::WideExact::from_le_bytes"⟩,
  ⟨.trustedStd, "aspis_core::r0::heap::filled"⟩,
  ⟨.owned .s7, "aspis_core::r0::domain::FibreIndex::new"⟩,
  ⟨.owned .s7, "aspis_r1_cost_probe::fast_domain::fibre_point"⟩,
  ⟨.owned .s5, "aspis_core::field::M31::inv"⟩,
  ⟨.owned .s7, "aspis_r1_cost_probe::fast_domain::line_node"⟩,
  ⟨.owned .s5, "aspis_core::field::M31::mul"⟩,
  ⟨.owned .s5, "aspis_core::field::M31::double"⟩,
  ⟨.owned .s5, "aspis_core::field::M31::sub"⟩,
  ⟨.owned .s3, "aspis_r1_cost_probe::weights::Weights::new"⟩,
  ⟨.owned .s3, "aspis_r1_cost_probe::weights::Weights::pair"⟩,
  ⟨.owned .s7, "aspis_r1_cost_probe::trace::value"⟩,
  ⟨.owned .s5, "aspis_core::field::QM31::from_le_bytes"⟩,
  ⟨.owned .s5, "aspis_core::<field::M31 as core::clone::Clone>::clone"⟩,
  ⟨.owned .s4, "aspis_r1_cost_probe::fast_dots::four_dots"⟩,
  ⟨.owned .s5, "aspis_core::field::M31::reduce_u64"⟩,
  ⟨.owned .s3, "aspis_r1_cost_probe::weights::field"⟩,
  ⟨.owned .s5, "aspis_core::field::wide_exact::WideExact::add"⟩,
  ⟨.owned .s5, "aspis_core::field::wide_exact::WideExact::mul_m31"⟩,
  ⟨.owned .s5, "aspis_core::<field::wide_exact::WideExact as core::cmp::PartialEq>::eq"⟩,
  ⟨.owned .s8, "aspis_r1_cost_probe::fast_pairing::EbyKDot::new"⟩,
  ⟨.owned .s8, "aspis_r1_cost_probe::fast_pairing::EbyKDot::finish"⟩,
  ⟨.owned .s8, "aspis_r1_cost_probe::fast_pairing::EbyKDot::push"⟩,
  ⟨.owned .s5, "aspis_core::<field::QM31 as core::clone::Clone>::clone"⟩,
  ⟨.owned .s5, "aspis_core::<field::M31 as core::cmp::PartialEq>::eq"⟩,
  ⟨.owned .s5, "aspis_core::field::wide_exact::WideExact::sub"⟩,
  ⟨.owned .s5, "aspis_core::field::wide_exact::WideExact::mul"⟩,
  ⟨.owned .s5, "aspis_core::field::wide_exact::WideExact::mul_qm31"⟩,
  ⟨.owned .s5, "aspis_core::field::QM31::mul"⟩,
  ⟨.owned .s5, "aspis_core::field::wide_exact::WideExact::from_qm31"⟩,
  ⟨.owned .s5, "aspis_core::<field::wide_exact::WideExact as r0::scalar::CodeField>::from_m31"⟩,
  ⟨.owned .multiproof, "aspis_core::state_only_private_merkle::private_leaf_hash_with_digest"⟩,
  ⟨.owned .multiproof, "aspis_core::r0::merkle::parent_with_digest"⟩,
  ⟨.owned .s5, "aspis_core::<field::wide_exact::WideExact as r0::scalar::CodeField>::add"⟩,
  ⟨.owned .s5, "aspis_core::<field::wide_exact::WideExact as r0::scalar::CodeField>::sub"⟩,
  ⟨.owned .s5, "aspis_core::<field::wide_exact::WideExact as r0::scalar::CodeField>::neg"⟩,
  ⟨.owned .s5, "aspis_core::<field::wide_exact::WideExact as r0::scalar::CodeField>::mul"⟩,
  ⟨.owned .s5, "aspis_core::<field::wide_exact::WideExact as r0::scalar::CodeField>::try_inv"⟩,
  ⟨.owned .s5, "aspis_core::<field::wide_exact::WideExact as core::clone::Clone>::clone"⟩]

theorem heap_filled_mem : OraclePortStdAllocation.heapFilledSite ∈ inventory := by
  simp [inventory, OraclePortStdAllocation.heapFilledSite]

#print axioms heap_filled_mem
end AspisR1.OraclePortS10InventoryStd
