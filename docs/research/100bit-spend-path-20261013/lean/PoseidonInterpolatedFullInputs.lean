import PoseidonInterpolatedFullSource
import PoseidonThreeConstantColumnsModel

/-! Actual weights and table reads feeding both full-round constant arrays.
The enclosing wrapper factor equation keeps subsequent round calls explicit. -/
set_option autoImplicit false
namespace AspisR1.PoseidonInterpolatedFullInputs
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep

def weights (local1 : State) : AspisR1.PoseidonThreeConstantColumnStep.Weights := Array.make 3#usize
  [cell local1 (⟨1,by decide⟩ : Fin 16), cell local1 (⟨9,by decide⟩ : Fin 16),
    cell local1 (⟨10,by decide⟩ : Fin 16)]

def prepare (local1 : State) : Result (State × State) := do
  let w0 ← Array.index_usize local1 1#usize
  let w1 ← Array.index_usize local1 9#usize
  let w2 ← Array.index_usize local1 10#usize
  let c0 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 2#usize
  let c1 ← Array.index_usize poseidon2.EXTERNAL_FINAL 0#usize
  let c2 ← Array.index_usize poseidon2.EXTERNAL_FINAL 2#usize
  let even ← state_only_poseidon.interpolate_three_constant_columns (Array.make 3#usize [w0,w1,w2]) c0 c1 c2
  let d0 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 3#usize
  let d1 ← Array.index_usize poseidon2.EXTERNAL_FINAL 1#usize
  let d2 ← Array.index_usize poseidon2.EXTERNAL_FINAL 3#usize
  let odd ← state_only_poseidon.interpolate_three_constant_columns (Array.make 3#usize [w0,w1,w2]) d0 d1 d2
  pure (even,odd)

def evenModel (local1 : State) (j : Fin 16) : Exact :=
  Decode (cell local1 (⟨1,by decide⟩ : Fin 16)) * R0P.poseidonExternalInitial (⟨2,by decide⟩ : Fin 4) j +
  Decode (cell local1 (⟨9,by decide⟩ : Fin 16)) * R0P.poseidonExternalFinal (⟨0,by decide⟩ : Fin 4) j +
  Decode (cell local1 (⟨10,by decide⟩ : Fin 16)) * R0P.poseidonExternalFinal (⟨2,by decide⟩ : Fin 4) j

def oddModel (local1 : State) (j : Fin 16) : Exact :=
  Decode (cell local1 (⟨1,by decide⟩ : Fin 16)) * R0P.poseidonExternalInitial (⟨3,by decide⟩ : Fin 4) j +
  Decode (cell local1 (⟨9,by decide⟩ : Fin 16)) * R0P.poseidonExternalFinal (⟨1,by decide⟩ : Fin 4) j +
  Decode (cell local1 (⟨10,by decide⟩ : Fin 16)) * R0P.poseidonExternalFinal (⟨3,by decide⟩ : Fin 4) j

theorem weights_canonical (local1 : State) (hl : CanonicalState local1) :
    AspisR1.PoseidonThreeConstantColumnStep.CanonicalWeights (weights local1) := by
  intro i
  fin_cases i
  · exact hl ⟨1,by decide⟩
  · exact hl ⟨9,by decide⟩
  · exact hl ⟨10,by decide⟩

theorem prepare_success (local1 : State) (hl : CanonicalState local1) :
    ∃ even odd : State, prepare local1 = .ok (even,odd) ∧ CanonicalState even ∧ CanonicalState odd ∧
      (∀ j : Fin 16, Decode (cell even j) = evenModel local1 j) ∧
      (∀ j : Fin 16, Decode (cell odd j) = oddModel local1 j) := by
  have hread1 : Array.index_usize local1 1#usize = .ok (cell local1 (⟨1,by decide⟩ : Fin 16)) :=
    AspisR1.ExtractedMaskHornerStep.array_index_usize_ok local1 1#usize (by decide)
  have hread9 : Array.index_usize local1 9#usize = .ok (cell local1 (⟨9,by decide⟩ : Fin 16)) :=
    AspisR1.ExtractedMaskHornerStep.array_index_usize_ok local1 9#usize (by decide)
  have hread10 : Array.index_usize local1 10#usize = .ok (cell local1 (⟨10,by decide⟩ : Fin 16)) :=
    AspisR1.ExtractedMaskHornerStep.array_index_usize_ok local1 10#usize (by decide)
  have hi2 : Array.index_usize poseidon2.EXTERNAL_INITIAL 2#usize = .ok (AspisR1.PoseidonInitialConstantsExact.row ⟨2,by decide⟩) :=
    AspisR1.PoseidonInitialConstantsExact.row_source_read 2#usize (by decide)
  have hi3 : Array.index_usize poseidon2.EXTERNAL_INITIAL 3#usize = .ok (AspisR1.PoseidonInitialConstantsExact.row ⟨3,by decide⟩) :=
    AspisR1.PoseidonInitialConstantsExact.row_source_read 3#usize (by decide)
  have hf0 : Array.index_usize poseidon2.EXTERNAL_FINAL 0#usize = .ok (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨0,by decide⟩) :=
    AspisR1.PoseidonRemainingConstantsExact.final_source_read 0#usize (by decide)
  have hf1 : Array.index_usize poseidon2.EXTERNAL_FINAL 1#usize = .ok (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨1,by decide⟩) :=
    AspisR1.PoseidonRemainingConstantsExact.final_source_read 1#usize (by decide)
  have hf2 : Array.index_usize poseidon2.EXTERNAL_FINAL 2#usize = .ok (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨2,by decide⟩) :=
    AspisR1.PoseidonRemainingConstantsExact.final_source_read 2#usize (by decide)
  have hf3 : Array.index_usize poseidon2.EXTERNAL_FINAL 3#usize = .ok (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨3,by decide⟩) :=
    AspisR1.PoseidonRemainingConstantsExact.final_source_read 3#usize (by decide)
  obtain ⟨even,heven,hcanEven,hmodelEven⟩ := AspisR1.PoseidonThreeConstantColumnsModel.source_success
    (weights local1) (AspisR1.PoseidonInitialConstantsExact.row ⟨2,by decide⟩) (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨0,by decide⟩) (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨2,by decide⟩)
    (weights_canonical local1 hl) (AspisR1.PoseidonInitialConstantsExact.row_canonical _) (AspisR1.PoseidonRemainingConstantsExact.final_canonical _) (AspisR1.PoseidonRemainingConstantsExact.final_canonical _)
  obtain ⟨odd,hodd,hcanOdd,hmodelOdd⟩ := AspisR1.PoseidonThreeConstantColumnsModel.source_success
    (weights local1) (AspisR1.PoseidonInitialConstantsExact.row ⟨3,by decide⟩) (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨1,by decide⟩) (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨3,by decide⟩)
    (weights_canonical local1 hl) (AspisR1.PoseidonInitialConstantsExact.row_canonical _) (AspisR1.PoseidonRemainingConstantsExact.final_canonical _) (AspisR1.PoseidonRemainingConstantsExact.final_canonical _)
  refine ⟨even,odd,?_,hcanEven,hcanOdd,?_,?_⟩
  · simp only [prepare,hread1,hread9,hread10,hi2,hf0,hf2,hi3,hf1,hf3,bind_tc_ok]
    change (do
      let even ← state_only_poseidon.interpolate_three_constant_columns (weights local1)
        (AspisR1.PoseidonInitialConstantsExact.row ⟨2,by decide⟩) (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨0,by decide⟩) (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨2,by decide⟩)
      let odd ← state_only_poseidon.interpolate_three_constant_columns (weights local1)
        (AspisR1.PoseidonInitialConstantsExact.row ⟨3,by decide⟩) (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨1,by decide⟩) (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨3,by decide⟩)
      pure (even,odd)) = .ok (even,odd)
    simp only [heven,hodd,bind_tc_ok]
    rfl
  · intro j
    have h := hmodelEven j
    change Decode (cell even j) =
      Decode (cell local1 (⟨1,by decide⟩ : Fin 16)) * ((cell (AspisR1.PoseidonInitialConstantsExact.row ⟨2,by decide⟩) j).val : Exact) +
      Decode (cell local1 (⟨9,by decide⟩ : Fin 16)) * ((cell (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨0,by decide⟩) j).val : Exact) +
      Decode (cell local1 (⟨10,by decide⟩ : Fin 16)) * ((cell (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨2,by decide⟩) j).val : Exact) at h
    rw [AspisR1.PoseidonInitialConstantsExact.row_model,AspisR1.PoseidonRemainingConstantsExact.final_model,AspisR1.PoseidonRemainingConstantsExact.final_model] at h
    exact h
  · intro j
    have h := hmodelOdd j
    change Decode (cell odd j) =
      Decode (cell local1 (⟨1,by decide⟩ : Fin 16)) * ((cell (AspisR1.PoseidonInitialConstantsExact.row ⟨3,by decide⟩) j).val : Exact) +
      Decode (cell local1 (⟨9,by decide⟩ : Fin 16)) * ((cell (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨1,by decide⟩) j).val : Exact) +
      Decode (cell local1 (⟨10,by decide⟩ : Fin 16)) * ((cell (AspisR1.PoseidonRemainingConstantsExact.finalRow ⟨3,by decide⟩) j).val : Exact) at h
    rw [AspisR1.PoseidonInitialConstantsExact.row_model,AspisR1.PoseidonRemainingConstantsExact.final_model,AspisR1.PoseidonRemainingConstantsExact.final_model] at h
    exact h

theorem wrapper_factor (state local1 : State) :
    state_only_poseidon.interpolated_full_pair_packed state local1 = (do
      let (even,odd) ← prepare local1
      let state1 ← state_only_poseidon.full_round state even
      state_only_poseidon.full_round_packed state1 odd) := by
  simp only [state_only_poseidon.interpolated_full_pair_packed,prepare,bind_assoc_eq,bind_tc_ok]
  rfl

#print axioms weights_canonical
#print axioms prepare_success
#print axioms wrapper_factor
end AspisR1.PoseidonInterpolatedFullInputs
