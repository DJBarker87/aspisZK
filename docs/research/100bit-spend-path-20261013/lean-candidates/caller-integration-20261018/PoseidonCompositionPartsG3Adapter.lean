import AspisR1.CompositionPartsAfterValidationSource
import PoseidonCandidateProjectedActualG3PackedFamilyV3
import AspisR1.PoseidonSelectorsSource

/-! Adapter from the exact callable interface of the retained
`CompositionPartsAfterValidation.run` source cut to the checked final G3
candidate evaluator theorem. The caller supplies Pool selectors; the actual
`poseidon_selectors` source conversion is executed before the candidate
evaluator QName. This file does not claim the adapter is yet wired into the
production Rust caller or that the candidate Rust snapshot is production. -/
set_option autoImplicit false
namespace AspisR1.PoseidonCompositionPartsG3Adapter
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Openings := AspisR1.CompositionPartsAfterValidation.Openings
abbrev CallerSelectors := AspisR1.CompositionPartsAfterValidation.Selectors
abbrev CandidateSelectors := state_only_poseidon.StateOnlyPoseidonSelectors
abbrev Packed := Array QM 4#usize

/-- The concrete callable supplied to the continuation caller: preserve its
Pool-selector argument and run the retained selector conversion before the
new evaluator QName. -/
def candidatePoseidonAt : AspisR1.CompositionPartsAfterValidation.PoseidonAt := fun openings selectors => do
  let projected ← AspisR1.PoseidonSelectorsSource.source selectors
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected openings projected

/-- The caller's exact boxed selector result can be passed to the concrete
candidate oracle. The final G3 theorem supplies the only evaluator/family
premise; no separate leading/full branch success hypotheses are introduced. -/
theorem boxed_call_candidate_poseidon_at_packed_family
    (openings : Openings) (point : Array QM 10#usize)
    (hpoint : AspisR1.SumHighInnerLoop.CanonicalArray point)
    (hopenZ : AspisR1.SumHighInnerLoop.CanonicalArray openings.z)
    (hopenSucc : AspisR1.SumHighInnerLoop.CanonicalArray openings.succ_z)
    (hopenXor : AspisR1.SumHighInnerLoop.CanonicalArray openings.xor12_z) :
    ∃ selectors : CallerSelectors, ∃ projected : CandidateSelectors,
      ∃ internal : AspisR1.PoseidonCandidateProjectedActualG3.State,
      ∃ out : Packed,
        AspisR1.CompositionPartsAfterValidation.Selectors.boxed_at_point point = .ok selectors ∧
        AspisR1.PoseidonSelectorsSource.source selectors = .ok projected ∧
        state_only_poseidon.interpolated_internal_pair openings.z projected.«local» = .ok internal ∧
        candidatePoseidonAt openings selectors = .ok out ∧
        (∀ i : Fin 4, AspisR1.PoseidonCandidateProjectedActualG3.Canonical
          (out.val[i.val]'(by simpa [out.property] using i.isLt))) ∧
        ∀ pub : R0P.Public AspisWideTower.WideExact,
          (R0P.poseidonPackedFamily
            (K := AspisWideTower.WideExact)
            AspisR1.ExtractedMaskSemanticBridgeConcrete.packBasis).residuals pub
            (AspisR1.ValueFamilyFieldTransport.mapOpenings
              AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
              (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings))
            (fun b => AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
              (AspisR1.SelectorValueLaneModelComposition.pointSelector point b)) =
          List.ofFn (fun g : Fin 4 => AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
            (AspisR1.ExtractedMaskQM31Exact.decode
              (AspisR1.PoseidonClosure2ArrayExact.cell4 out g))) := by
  obtain ⟨selectorInput, projected, internal, out, hbox, heval, hselectors,
      hinternal, hout, hcanonical, hfamily⟩ :=
    AspisR1.PoseidonCandidateProjectedActualG3PackedFamilyV3
      .canonical_point_actual_boxed_g3_packed_family
        openings point hpoint hopenZ hopenSucc hopenXor
  refine ⟨selectorInput, projected, internal, out,
    hbox, hselectors, hinternal, ?_, hcanonical, hfamily⟩
  change (do
    let projected ← AspisR1.PoseidonSelectorsSource.source selectorInput
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected openings projected) = .ok out
  rw [hselectors]
  exact heval

/-- Once the caller has already obtained its boxed selector value, the
existential selector returned above is forced to be that same value by
injectivity of the successful-result constructor. This version is convenient
for composing directly with `CompositionPartsAfterValidation.run`. -/
theorem fixed_boxed_selectors_candidate_poseidon_at_packed_family
    (openings : Openings) (point : Array QM 10#usize)
    (selectors : CallerSelectors)
    (hbox : AspisR1.CompositionPartsAfterValidation.Selectors.boxed_at_point point = .ok selectors)
    (hpoint : AspisR1.SumHighInnerLoop.CanonicalArray point)
    (hopenZ : AspisR1.SumHighInnerLoop.CanonicalArray openings.z)
    (hopenSucc : AspisR1.SumHighInnerLoop.CanonicalArray openings.succ_z)
    (hopenXor : AspisR1.SumHighInnerLoop.CanonicalArray openings.xor12_z) :
    ∃ projected : CandidateSelectors,
      ∃ internal : AspisR1.PoseidonCandidateProjectedActualG3.State,
      ∃ out : Packed,
        AspisR1.PoseidonSelectorsSource.source selectors = .ok projected ∧
        state_only_poseidon.interpolated_internal_pair openings.z projected.«local» = .ok internal ∧
        candidatePoseidonAt openings selectors = .ok out ∧
        (∀ i : Fin 4, AspisR1.PoseidonCandidateProjectedActualG3.Canonical
          (out.val[i.val]'(by simpa [out.property] using i.isLt))) ∧
        ∀ pub : R0P.Public AspisWideTower.WideExact,
          (R0P.poseidonPackedFamily
            (K := AspisWideTower.WideExact)
            AspisR1.ExtractedMaskSemanticBridgeConcrete.packBasis).residuals pub
            (AspisR1.ValueFamilyFieldTransport.mapOpenings
              AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
              (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings))
            (fun b => AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
              (AspisR1.SelectorValueLaneModelComposition.pointSelector point b)) =
          List.ofFn (fun g : Fin 4 => AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
            (AspisR1.ExtractedMaskQM31Exact.decode
              (AspisR1.PoseidonClosure2ArrayExact.cell4 out g))) := by
  obtain ⟨selectorInput, projected, internal, out, hboxResult, hselectors,
      hinternal, hout, hcanonical, hfamily⟩ :=
    boxed_call_candidate_poseidon_at_packed_family
      openings point hpoint hopenZ hopenSucc hopenXor
  have hsame : selectorInput = selectors := by
    have heq : Result.ok selectorInput = Result.ok selectors := hboxResult.symm.trans hbox
    injection heq with h
    exact h
  subst selectorInput
  exact ⟨projected, internal, out, hselectors, hinternal, hout, hcanonical, hfamily⟩

#print axioms boxed_call_candidate_poseidon_at_packed_family
end AspisR1.PoseidonCompositionPartsG3Adapter
