import PoseidonCandidateProjectedWrapperFactorV8
import AspisR1.PoseidonActualPreparedWeights
import AspisR1.PoseidonClosure2ArrayExact
import ExtractedMaskPreparedState
import ExtractedMaskQM31Exact

/- Successful-call adapter for the pinned candidate projected-wrapper cut.
   It assumes only that the three actual packed calls return their outputs and
   that those outputs have the exact callback-input canonicality. The separate
   wrapper-factor theorem has no success premise and preserves failure order. -/
set_option autoImplicit false
namespace AspisR1.PoseidonCandidateProjectedWrapperSuccess
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonCandidateProjectedWrapperFactor
open AspisR1.PoseidonCandidateProjectedCallbackSource

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev PreparedFor := AspisR1.ExtractedMaskPreparedState.PreparedFor
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

private def localAt (a : Array QM 16#usize) (i : Fin 16) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
private def get4 (a : Array QM 4#usize) (i : Usize) (hi : i.val < 4) : QM :=
  a.val[i.val]'(by simpa [a.property] using hi)
private def get3 (a : Array QM 3#usize) (i : Fin 3) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
private def getPrepared3 (a : Array Prepared 3#usize) (i : Fin 3) : Prepared :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

/-- The candidate wrapper succeeds and its result satisfies the existing
    closure-array model whenever each earlier packed call actually succeeds. -/
theorem success_from_component_success
    (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : state_only_poseidon.StateOnlyPoseidonSelectors)
    (leading : Array QM 4#usize) (full : Array QM 4#usize)
    (internal : Array QM 16#usize)
    (hblock : Canonical selectors.block)
    (hlocal : ∀ i : Fin 16, Canonical (localAt selectors.local i))
    (hsuccessor : ∀ i : Fin 16, Canonical
      (openings.succ_z.val[i.val]'(by simpa [openings.succ_z.property] using i.isLt)))
    (hinternal : ∀ i : Fin 16, Canonical
      (internal.val[i.val]'(by simpa [internal.property] using i.isLt)))
    (hleading : ∀ (i : Usize) (hi : i.val < 4), Canonical (get4 leading i hi))
    (hfull : ∀ (i : Usize) (hi : i.val < 4), Canonical (get4 full i hi))
    (hleadingCall : state_only_poseidon.leading_pair_packed openings = .ok leading)
    (hfullCall : state_only_poseidon.interpolated_full_pair_packed
      openings.z selectors.local = .ok full)
    (hinternalCall : state_only_poseidon.interpolated_internal_pair
      openings.z selectors.local = .ok internal) :
    ∃ leadingLow fullLow internalLow : QM,
    ∃ weights : Array QM 3#usize, ∃ out : Array QM 4#usize,
      weights = Array.make 3#usize [leadingLow,fullLow,internalLow] ∧
      Decode leadingLow = Decode (localAt selectors.local 0) ∧
      Decode fullLow = AspisR1.PoseidonExplicitLowWeightFold.fullLow
        (fun i => Decode (localAt selectors.local i)) ∧
      Decode internalLow = AspisR1.PoseidonExplicitLowWeightFold.internalLow
        (fun i => Decode (localAt selectors.local i)) ∧
      candidate_projected_source openings selectors = .ok out ∧
      (∀ i : Fin 4, Canonical
        (out.val[i.val]'(by simpa [out.property] using i.isLt))) ∧
      ∀ i : Fin 4, Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 out i) =
        AspisR1.PoseidonClosure2ArrayExact.model openings internal selectors.block
          weights leading full i := by
  obtain ⟨fullLow, hfullLow, hfullLowCan, hfullLowDecode⟩ :=
    AspisR1.PoseidonActualLowWeights.fullLow_source_success selectors.local hlocal
  obtain ⟨internalLow, hinternalLow, hinternalLowCan, hinternalLowDecode⟩ :=
    AspisR1.PoseidonActualLowWeights.internalLow_source_success selectors.local hlocal
  let leadingLow : QM := localAt selectors.local 0
  have hleadingLowCan : Canonical leadingLow := hlocal 0
  have hread0 : Array.index_usize selectors.local 0#usize = .ok leadingLow := by
    simpa [leadingLow, localAt] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok selectors.local 0#usize (by decide)
  obtain ⟨p0,p1,p2,hmap,hp0,hp1,hp2⟩ :=
    AspisR1.PoseidonPreparedWeightMap.prepared_map_three
      leadingLow fullLow internalLow hleadingLowCan hfullLowCan hinternalLowCan
  let weights : Array QM 3#usize := Array.make 3#usize [leadingLow,fullLow,internalLow]
  let preparedWeights : Array Prepared 3#usize := Array.make 3#usize [p0,p1,p2]
  obtain ⟨preparedBlock,hnew,hprepared⟩ :=
    AspisR1.ExtractedMaskPreparedState.current_prepared_new selectors.block hblock
  have hlow : actual_low_prelude selectors.local = .ok (leadingLow,fullLow,internalLow) := by
    simp only [actual_low_prelude, hread0, hfullLow, hinternalLow, bind_tc_ok]
  have hmapExact : core.array.Array.map (BuiltinFnMut QM Prepared)
      (Array.make 3#usize [leadingLow,fullLow,internalLow])
      (field.PreparedQm31Multiplier.new) = .ok preparedWeights := by
    simpa [AspisR1.PoseidonPreparedWeightMap.Callback, AspisR1.PoseidonPreparedWeightMap.New,
      preparedWeights] using hmap
  have hweightsCan : ∀ i : Fin 3, Canonical (get3 weights i) := by
    intro i
    fin_cases i <;> simp [weights, get3, Array.make] <;> assumption
  have hweightsPrepared : ∀ i : Fin 3, PreparedFor
      (getPrepared3 preparedWeights i) (get3 weights i) := by
    intro i
    fin_cases i <;> simp [preparedWeights, weights, getPrepared3, get3, Array.make] <;>
      assumption
  obtain ⟨out,hrun,hcan,hmodel⟩ :=
    AspisR1.PoseidonClosure2ArrayExact.source_success openings internal
      preparedBlock selectors.block preparedWeights weights leading full hblock hprepared
      hweightsCan hweightsPrepared hsuccessor hinternal hleading hfull
  have hcallbackRun : candidate_array
      (openings, internal, preparedBlock, preparedWeights, leading, full) =
        AspisR1.PoseidonClosure2ArrayExact.run openings internal preparedBlock
          preparedWeights weights leading full := by
    rfl
  refine ⟨leadingLow,fullLow,internalLow,weights,out,rfl,rfl,hfullLowDecode,hinternalLowDecode,?_,hcan,?_⟩
  · simp only [candidate_projected_source, hlow, bind_tc_ok, hleadingCall,
      hfullCall, hinternalCall]
    change (do
      let prepared_weights ← core.array.Array.map (BuiltinFnMut QM Prepared)
        (Array.make 3#usize [leadingLow,fullLow,internalLow])
        (field.PreparedQm31Multiplier.new)
      let prepared_block ← field.PreparedQm31Multiplier.new selectors.block
      candidate_array (openings, internal, prepared_block, prepared_weights, leading, full)) = .ok out
    rw [hmapExact, hnew]
    simp only [bind_tc_ok]
    rw [hcallbackRun, hrun]
  · intro i
    exact hmodel i

#print axioms success_from_component_success
end AspisR1.PoseidonCandidateProjectedWrapperSuccess
