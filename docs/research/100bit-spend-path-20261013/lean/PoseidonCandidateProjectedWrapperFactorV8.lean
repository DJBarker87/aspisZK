import AspisR1.PoseidonActualPreparedWeights
import PoseidonCandidateProjectedCallbackSourceV4
import AspisR1.PoseidonSelectorsSource
import PoseidonLeadingSourceDeclarationsV5
import PoseidonInterpolatedFullSource
import PoseidonInternalPairSource

/- Exact evaluator-wrapper source factor for candidate Rust SHA
   82d54bbade8d81899c64ede23befce8b240b881d61b144e769c0d0e16ab5cff9,
   extracted candidate Funs SHA
   f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c,
   lines 2691-2733. This cut retains source sequencing: all low reads/folds,
   then leading/full/internal packed calls, then prepared-weight map, prepared
   block, and callback array. No success premise is used to commute operations.
-/
set_option autoImplicit false
namespace AspisR1.PoseidonCandidateProjectedWrapperFactor
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonCandidateProjectedCallbackSource

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := state_only_poseidon.StateOnlyPoseidonSelectors

/-- Exact source-order low-weight prelude, with the source ZERO additions
    and low reads represented by their already pinned source cuts. -/
def actual_low_prelude (localWeights : Array QM 16#usize) : Result (QM × QM × QM) := do
  let leadingLow ← Array.index_usize localWeights 0#usize
  let fullLow ← AspisR1.PoseidonActualLowWeights.fullLowSource localWeights
  let internalLow ← AspisR1.PoseidonActualLowWeights.internalLowSource localWeights
  .ok (leadingLow, fullLow, internalLow)

/-- The candidate evaluator source body, with only its exact callback body
    factored to `candidate_array`. Each preceding Result-producing call stays
    in the same order as the pinned source. -/
def candidate_projected_source (openings : Openings) (selectors : Selectors) :
    Result (Array QM 4#usize) := do
  let (leadingLow, fullLow, internalLow) ← actual_low_prelude selectors.local
  let leading ← state_only_poseidon.leading_pair_packed openings
  let full ← state_only_poseidon.interpolated_full_pair_packed openings.z selectors.local
  let internal ← state_only_poseidon.interpolated_internal_pair openings.z selectors.local
  let prepared_weights ←
    core.array.Array.map
      (BuiltinFnMut QM Prepared)
      (Array.make 3#usize [leadingLow, fullLow, internalLow])
      (field.PreparedQm31Multiplier.new)
  let prepared_block ← field.PreparedQm31Multiplier.new selectors.block
  candidate_array
    (openings, internal, prepared_block, prepared_weights, leading, full)

/-- Explicit un-factored low reads/folds from the evaluator's pinned Funs
    source, retained as a local correspondence witness for the wrapper cut. -/
def candidate_projected_source_unfactored (openings : Openings) (selectors : Selectors) :
    Result (Array QM 4#usize) := do
  let leading_low ← Array.index_usize selectors.local 0#usize
  let q ← Array.index_usize selectors.local 1#usize
  let q1 ← field.QM31.add field.QM31.ZERO q
  let q2 ← Array.index_usize selectors.local 9#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize selectors.local 10#usize
  let full_low ← field.QM31.add q3 q4
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
  let internal_low ← field.QM31.add q16 q17
  let leading ← state_only_poseidon.leading_pair_packed openings
  let full ← state_only_poseidon.interpolated_full_pair_packed openings.z selectors.local
  let internal ← state_only_poseidon.interpolated_internal_pair openings.z selectors.local
  let prepared_weights ←
    core.array.Array.map
      (BuiltinFnMut QM Prepared)
      (Array.make 3#usize [leading_low, full_low, internal_low])
      (field.PreparedQm31Multiplier.new)
  let prepared_block ← field.PreparedQm31Multiplier.new selectors.block
  candidate_array
    (openings, internal, prepared_block, prepared_weights, leading, full)

theorem candidate_wrapper_factor_exact
    (openings : Openings) (selectors : Selectors) :
    candidate_projected_source_unfactored openings selectors =
      candidate_projected_source openings selectors := by
  simp only [candidate_projected_source_unfactored, candidate_projected_source,
    actual_low_prelude, AspisR1.PoseidonActualLowWeights.fullLowSource,
    AspisR1.PoseidonActualLowWeights.internalLowSource, bind_assoc_eq, bind_tc_ok]
  rfl

#print axioms candidate_wrapper_factor_exact
end AspisR1.PoseidonCandidateProjectedWrapperFactor
