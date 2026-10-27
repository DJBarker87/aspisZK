import RPu_FIy_Scaling
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_ScalingSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

theorem reached (packed out : Array NQ 24#usize) (o : Openings) (s : Selectors)
    (success : pool_v1.pair_forest_semantic_terminal.add_value_lanes packed o s=ok out) :
    ∃ (range scaled : Array NQ 33#usize) (selector : NQ) (packed1 : Array NQ 24#usize),
      FIy_ScaleReadback.run range selector=ok scaled ∧
      pool_v1.pair_forest_semantic_terminal.add_preweighted packed 49#usize scaled=ok packed1 ∧
      (canonical range → Canon selector → canonical scaled ∧
        decoded scaled=fun j=>decode selector*decoded range j) := by
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
  let scaled := into_iter_back (back im)
  have scaleRun : FIy_ScaleReadback.run range6 range_selector=ok scaled := by
    unfold FIy_ScaleReadback.run
    simp only [h_iter_into_iter_back,bind_tc_ok]
    change (do let (im,b) ← pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3 iter (fun x=>x) range_selector
               ok (into_iter_back (b im)))=ok scaled
    rw [h_im_back]
    rfl
  exact ⟨range6,scaled,range_selector,packed1,scaleRun,h_packed1,
    fun hc hs=>FIy_Scaling.value range6 scaled range_selector hc hs scaleRun⟩
#print axioms reached
end AspisR1.FIy_ScalingSource
end
