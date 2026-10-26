import FIx_ValueConservation
import FIx_ValueBitPrefix
import FIw_SelectorRow
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ValueConservationSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

theorem value (packed out : Array NQ 24#usize) (o : Openings) (s : Selectors)
    (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hh : canonical s.high) (hl : canonical s.low)
    (success : pool_v1.pair_forest_semantic_terminal.add_value_lanes packed o s=ok out) :
    ∃ (before : Array NQ 24#usize) (selector : NQ) (row base : Usize) (scalars : Array NQ 2#usize),
      16#usize*pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK=ok base ∧
      base+6#usize=ok row ∧ pool_v1.pair_forest_copy_terminal.Selectors.row s row=ok selector ∧
      FIx_ValueConservation.run selector o.z o.succ_z=ok scalars ∧
      pool_v1.pair_forest_semantic_terminal.add_preweighted before 82#usize scalars=ok out ∧
      canonical scalars ∧ scalars.val.map decode=FIx_ValueConservation.model
        (FIv_NativeArray.value s.high (row.val/16)*FIv_NativeArray.value s.low (row.val%16))
        (FIv_NativeArray.value o.z) (FIv_NativeArray.value o.succ_z) := by
  unfold pool_v1.pair_forest_semantic_terminal.add_value_lanes at success
  obtain ⟨value_selectors,h_value_selectors,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q,h_q,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q1,h_q1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q2,h_q2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q3,h_q3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q4,h_q4,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨range_selector,h_range_selector,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨openings1, range1⟩,h_openings1_range1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨openings2, range2⟩,h_openings2_range2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨openings3, range3⟩,h_openings3_range3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q5,h_q5,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q6,h_q6,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i,h_i,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q7,h_q7,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q8,h_q8,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q9,h_q9,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i1,h_i1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q10,h_q10,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨reconstructed,h_reconstructed,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q11,h_q11,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q12,h_q12,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨range4,h_range4,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q13,h_q13,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨range5,h_range5,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q14,h_q14,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨range6,h_range6,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨iter, into_iter_back⟩,h_iter_into_iter_back,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨im, back⟩,h_im_back,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨packed1,h_packed1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i2,h_i2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i3,h_i3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨conservation_selector,h_conservation_selector,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q15,h_q15,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q16,h_q16,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q17,h_q17,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q18,h_q18,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q19,h_q19,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q20,h_q20,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q21,h_q21,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q22,h_q22,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q23,h_q23,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q24,h_q24,success⟩ := FIv_Map.bind_success _ _ _ success
  have zero : canonical (Array.repeat 33#usize field.QM31.ZERO) := by
    intro x hx
    have same : x=field.QM31.ZERO := List.eq_of_mem_replicate hx
    rw [same]
    exact FIv_NativeValue.zero.1
  have v0 := FIx_ValueBits0.value 10 0#usize o openings1 _ range1 (by rfl) hz zero h_openings1_range1
  have e0 := v0.1
  subst openings1
  have v1 := FIx_ValueBits1.value 10 0#usize o openings2 range1 range2 (by rfl) hs v0.2.1 h_openings2_range2
  have e1 := v1.1
  subst openings2
  have v2 := FIx_ValueBits2.value 10 0#usize o openings3 range2 range3 (by rfl) hx v1.2.1 h_openings3_range3
  have e2 := v2.1
  subst openings3
  let scalars := Array.make 2#usize [q20,q24]
  have scalarCall : FIx_ValueConservation.run conservation_selector o.z o.succ_z=ok scalars := by
    simp only [FIx_ValueConservation.run,h_q15,h_q16,h_q17,h_q18,h_q19,h_q20,h_q21,h_q22,h_q23,h_q24,bind_tc_ok]
    rfl
  have selectorValue := FIw_SelectorRow.value_exact s i3 conservation_selector hh hl h_conservation_selector
  have meaning := FIx_ValueConservation.value conservation_selector o.z o.succ_z scalars selectorValue.1 hz hs scalarCall
  refine ⟨packed1,conservation_selector,i3,i2,scalars,h_i2,h_i3,h_conservation_selector,scalarCall,success,meaning.1,?_⟩
  rw [meaning.2,selectorValue.2]
#print axioms value
end AspisR1.FIx_ValueConservationSource
end
