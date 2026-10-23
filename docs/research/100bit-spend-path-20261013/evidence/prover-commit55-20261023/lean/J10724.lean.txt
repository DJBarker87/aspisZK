import PoseidonCandidateProjectedWrapperFactorV8

/-! Importable source-cut declaration for the actual projected evaluator QName.
This file does not import or overwrite the monolithic Funs/Types cache. It
retains the candidate wrapper's call order and uses the generated closure#2
callback constant at the final `core.array.from_fn` call. The parent Funs SHA
f1e258... is still an external source pin; this is a focused declaration slice,
not a replay of that full extraction. -/
set_option autoImplicit false
namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result

abbrev ProjectedOpenings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev ProjectedSelectors := state_only_poseidon.StateOnlyPoseidonSelectors
abbrev ProjectedQM := field.QM31
abbrev ProjectedPrepared := field.PreparedQm31Multiplier

/-- Literal projected-evaluator declaration slice: explicit ZERO-based lows,
packed helper call order, prepared-weight construction, and generated closure#2
callback. The Rust source excerpt pin is the explicit-low-fold extraction. -/
def state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
    (openings : ProjectedOpenings) (selectors : ProjectedSelectors) :
    Result (Array ProjectedQM 4#usize) := do
  let leadingLow ← Array.index_usize selectors.local 0#usize
  let q ← Array.index_usize selectors.local 1#usize
  let q1 ← field.QM31.add field.QM31.ZERO q
  let q2 ← Array.index_usize selectors.local 9#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize selectors.local 10#usize
  let fullLow ← field.QM31.add q3 q4
  let q5 ← Array.index_usize selectors.local 2#usize
  let q6 ← field.QM31.add field.QM31.ZERO q5
  let q7 ← Array.index_usize selectors.local 3#usize
  let q8 ← field.QM31.add q6 q7
  let q9 ← Array.index_usize selectors.local 4#usize
  let q10 ← field.QM31.add q8 q9
  let q11 ← Array.index_usize selectors.local 5#usize
  let q12 ← field.QM31.add q10 q11
  let q13 ← Array.index_usize selectors.local 6#usize
  let q14 ← field.QM31.add q12 q13
  let q15 ← Array.index_usize selectors.local 7#usize
  let q16 ← field.QM31.add q14 q15
  let q17 ← Array.index_usize selectors.local 8#usize
  let internalLow ← field.QM31.add q16 q17
  let leading ← state_only_poseidon.leading_pair_packed openings
  let full ← state_only_poseidon.interpolated_full_pair_packed openings.z selectors.local
  let internal ← state_only_poseidon.interpolated_internal_pair openings.z selectors.local
  let prepared_weights ←
    core.array.Array.map
      (BuiltinFnMut ProjectedQM ProjectedPrepared)
      (Array.make 3#usize [leadingLow, fullLow, internalLow])
      (field.PreparedQm31Multiplier.new)
  let prepared_block ← field.PreparedQm31Multiplier.new selectors.block
  array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
    AspisR1.PoseidonClosure2ArrayExact.Callback field.QM31.ZERO
    ((openings, internal, prepared_block, prepared_weights, leading, full) :
      AspisR1PoseidonProjectedClosure2Source.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2)

theorem evaluator_qname_eq_unfactored
    (openings : ProjectedOpenings) (selectors : ProjectedSelectors) :
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors =
      AspisR1.PoseidonCandidateProjectedWrapperFactor.candidate_projected_source_unfactored
        openings selectors := by
  simp only [state_only_poseidon.evaluate_state_only_poseidon_oracle_projected,
    AspisR1.PoseidonCandidateProjectedWrapperFactor.candidate_projected_source_unfactored]
  simp [AspisR1.PoseidonCandidateProjectedCallbackSource.candidate_array]
  rw [← AspisR1.PoseidonCandidateProjectedCallbackSource.candidate_callback_matches_closure2]
  all_goals (intros; rfl)

theorem evaluator_qname_eq_factored
    (openings : ProjectedOpenings) (selectors : ProjectedSelectors) :
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors =
      AspisR1.PoseidonCandidateProjectedWrapperFactor.candidate_projected_source
        openings selectors := by
  calc
    _ = AspisR1.PoseidonCandidateProjectedWrapperFactor.candidate_projected_source_unfactored
        openings selectors := evaluator_qname_eq_unfactored openings selectors
    _ = AspisR1.PoseidonCandidateProjectedWrapperFactor.candidate_projected_source
        openings selectors :=
      AspisR1.PoseidonCandidateProjectedWrapperFactor.candidate_wrapper_factor_exact
        openings selectors

#print axioms evaluator_qname_eq_factored
end AspisR1SelectedMaskProbe
