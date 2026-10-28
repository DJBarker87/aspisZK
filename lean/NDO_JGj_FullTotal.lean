import NDO_JGj_ThreeTotal
import NDO_JGj_QmRoundTotal
import RPv_FJe_FullWeights
import RPv_FJe_FinalConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_FullTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
theorem source (s l : State) (hs : canonical s) (hl : canonical l) :
    ∃ out,state_only_poseidon.interpolated_full_pair_packed s l=ok out ∧ canonical out := by
  obtain ⟨q0,r0,_⟩ := JFy_ArrayTotal.read l 1#usize (by decide) hl
  obtain ⟨q1,r1,_⟩ := JFy_ArrayTotal.read l 9#usize (by decide) hl
  obtain ⟨q2,r2,_⟩ := JFy_ArrayTotal.read l 10#usize (by decide) hl
  have hw := (FJe_FullWeights.value l q0 q1 q2 hl r0 r1 r2).1
  obtain ⟨even,re,ce⟩ := JGj_ThreeTotal.source _ _ _ _ hw
    (FJb_InitialConstants.bounded 2) (FJe_FinalConstants.bounded 0) (FJe_FinalConstants.bounded 2)
  obtain ⟨odd,ro,co⟩ := JGj_ThreeTotal.source _ _ _ _ hw
    (FJb_InitialConstants.bounded 3) (FJe_FinalConstants.bounded 1) (FJe_FinalConstants.bounded 3)
  obtain ⟨middle,rm,cm⟩ := JGj_QmRoundTotal.lazy s even hs ce
  obtain ⟨out,rf,cf⟩ := JGj_QmRoundTotal.packed middle odd cm co
  have e2 : Array.index_usize poseidon2.EXTERNAL_INITIAL 2#usize=ok (FJb_InitialConstants.row 2) := FJb_InitialConstants.read 2#usize (by decide)
  have e3 : Array.index_usize poseidon2.EXTERNAL_INITIAL 3#usize=ok (FJb_InitialConstants.row 3) := FJb_InitialConstants.read 3#usize (by decide)
  have f0 : Array.index_usize poseidon2.EXTERNAL_FINAL 0#usize=ok (FJe_FinalConstants.row 0) := FJe_FinalConstants.read 0#usize (by decide)
  have f1 : Array.index_usize poseidon2.EXTERNAL_FINAL 1#usize=ok (FJe_FinalConstants.row 1) := FJe_FinalConstants.read 1#usize (by decide)
  have f2 : Array.index_usize poseidon2.EXTERNAL_FINAL 2#usize=ok (FJe_FinalConstants.row 2) := FJe_FinalConstants.read 2#usize (by decide)
  have f3 : Array.index_usize poseidon2.EXTERNAL_FINAL 3#usize=ok (FJe_FinalConstants.row 3) := FJe_FinalConstants.read 3#usize (by decide)
  refine ⟨out,?_,cf⟩
  unfold state_only_poseidon.interpolated_full_pair_packed
  rw [r0,bind_tc_ok,r1,bind_tc_ok,r2,bind_tc_ok,e2,bind_tc_ok,f0,bind_tc_ok,f2,bind_tc_ok]
  change (do
    let even ← state_only_poseidon.interpolate_three_constant_columns (FJe_FullWeights.weights q0 q1 q2) _ _ _
    let a3 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 3#usize
    let a4 ← Array.index_usize poseidon2.EXTERNAL_FINAL 1#usize
    let a5 ← Array.index_usize poseidon2.EXTERNAL_FINAL 3#usize
    let odd ← state_only_poseidon.interpolate_three_constant_columns (FJe_FullWeights.weights q0 q1 q2) a3 a4 a5
    let middle ← state_only_poseidon.full_round s even
    state_only_poseidon.full_round_packed middle odd)=ok out
  rw [re,bind_tc_ok,e3,bind_tc_ok,f1,bind_tc_ok,f3,bind_tc_ok,ro,bind_tc_ok,rm,bind_tc_ok,rf]
#print axioms source
end AspisR1.JGj_FullTotal
end
