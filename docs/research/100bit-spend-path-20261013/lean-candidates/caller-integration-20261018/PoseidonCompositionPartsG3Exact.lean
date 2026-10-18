import PoseidonCompositionPartsG3Adapter
import AspisR1.CompositionPartsAfterValidationExact

/-! Discharge the retained continue-branch caller's Poseidon contract using
its actual candidate source computation. Canonical caller inputs and successful
public preparation remain explicit; whole production reachability is separate. -/
set_option autoImplicit false
namespace AspisR1.PoseidonCompositionPartsG3Exact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CompositionPartsAfterValidation
open AspisR1.SemanticCompositionCoefficients
open AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy
open scoped BigOperators
abbrev QM := field.QM31
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Statement := AspisR1TerminalDecoder.PublicBinding.Statement
abbrev f := AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
abbrev candidatePoseidonAt := AspisR1.PoseidonCompositionPartsG3Adapter.candidatePoseidonAt
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev lane := AspisR1.PoseidonExternalPackedModel.lane

def exactPoseidonModel (point : Array QM 10#usize)
    (openings : Openings) (_selectors : Selectors) (g : Fin 4) : ExactQM :=
  R0P.poseidonPackingFormula
    AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis
    AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis (fun j =>
      R0P.poseidonScalarResidual
        (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings)
        (R0P.g2SumHigh (pointSelector point) 0 57 (by omega))
        (R0P.g2Low (pointSelector point)) (lane g j))

/-- The successful candidate call has the literal exact-tower model required
by the existing 29-coefficient caller theorem. Injectivity is only of the
field embedding ExactQM -> WideExact, never of the four-way packing formula. -/
theorem candidate_contract
    (point : Array QM 10#usize) (openings : Openings) (selectors : Selectors)
    (hpoint : CanonicalArray point)
    (hbox : Selectors.boxed_at_point point = .ok selectors)
    (hz : CanonicalArray openings.z)
    (hsucc : CanonicalArray openings.succ_z)
    (hxor : CanonicalArray openings.xor12_z) :
    ∃ value : Array QM 4#usize,
      candidatePoseidonAt openings selectors = .ok value ∧
      CanonicalArray value ∧ ∀ i : Fin 4,
        decode (value.val[i.val]'(by simpa [value.property] using i.isLt)) =
          exactPoseidonModel point openings selectors i := by
  obtain ⟨projected, internal, value, hselectors, hinternal, hsource,
      hcanonical, hwide⟩ :=
    AspisR1.PoseidonCandidateProjectedActualG3.actual_boxed_candidate_g3
      openings point selectors hpoint hz hsucc hxor hbox
  have hcall : candidatePoseidonAt openings selectors = .ok value := by
    unfold candidatePoseidonAt
      AspisR1.PoseidonCompositionPartsG3Adapter.candidatePoseidonAt
    rw [hselectors]
    change state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
      openings projected = .ok value
    rw [AspisR1SelectedMaskProbe.evaluator_qname_eq_factored]
    exact hsource
  refine ⟨value, hcall, hcanonical, ?_⟩
  intro i
  have htransport := AspisR1.PoseidonCandidateScalarResidualWide.map_scalar_residual_pack
    (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings)
    (R0P.g2SumHigh (pointSelector point) 0 57 (by omega))
    (R0P.g2Low (pointSelector point)) i
  have hmodel : f (decode (AspisR1.PoseidonClosure2ArrayExact.cell4 value i)) =
      f (exactPoseidonModel point openings selectors i) :=
    (hwide i).trans htransport.symm
  exact f.injective hmodel

theorem run_candidate_success
    (point : Array QM 10#usize) (s : Statement)
    (claims : Array QM 84#usize) (lambda chi theta : QM)
    (hpoint : CanonicalArray point) (hclaims : CanonicalArray claims)
    (hlambda : CanonicalQM lambda) (hchi : CanonicalQM chi) (htheta : CanonicalQM theta)
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (c1 : Array U8 32#usize)
    (outTranscript : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (hprep : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)
      hash c1 = .ok (.Ok outTranscript)) :
    ∃ (openings : Openings) (selectors : Selectors)
      (maskOnly : Array QM 10#usize) (helper out q active : QM),
      (∀ i : Fin 16, openings.z.val[i.val]'(by simpa [openings.z.property] using i.isLt) =
        claims.val[i.val]'(by have := i.isLt; simpa [claims.property] using (show i.val < 84 by omega))) ∧
      (∀ i : Fin 16, openings.succ_z.val[i.val]'(by simpa [openings.succ_z.property] using i.isLt) =
        claims.val[28+i.val]'(by have := i.isLt; simpa [claims.property] using (show 28+i.val < 84 by omega))) ∧
      (∀ i : Fin 16, openings.xor12_z.val[i.val]'(by simpa [openings.xor12_z.property] using i.isLt) =
        claims.val[56+i.val]'(by have := i.isLt; simpa [claims.property] using (show 56+i.val < 84 by omega))) ∧
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors ∧
      pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize 26#usize = .ok helper ∧
      run candidatePoseidonAt (copyFromStatement s) claims point lambda chi theta =
        .ok (.Ok (out, openings.z, maskOnly, q, helper, active)) ∧
      CanonicalQM out ∧ CanonicalQM q ∧ CanonicalQM active ∧
      decode out = ∑ i : Fin 29, decode theta ^ i.val *
        lanesFromModels (exactPoseidonModel point openings selectors)
          (semanticLane24 (copyFromStatement s) openings point)
          (R0P.copyEvaluateWithSelectors
            (AspisR1.CopyEndpointExact.decodedCells openings.z) (decode helper)
            (AspisR1.CopyEndpointExact.modelSelectors selectors) (decode lambda) (decode chi)
            (copyFromStatement s).transition.live_snapshot.next_pair_index.val
            (AspisR1.CopyLinkWeightExact.modelVariant (copyVariant (copyFromStatement s).variant))).1 i := by
  apply AspisR1.CompositionPartsAfterValidationExact.run_success_of_poseidon_contract
    candidatePoseidonAt (exactPoseidonModel point) point s claims lambda chi theta
    hpoint hclaims hlambda hchi htheta _ D hash c1 outTranscript hprep
  intro openings selectors hbox hz hsucc hxor
  exact candidate_contract point openings selectors hpoint hbox hz hsucc hxor

#print axioms candidate_contract
#print axioms run_candidate_success
end
end AspisR1.PoseidonCompositionPartsG3Exact
