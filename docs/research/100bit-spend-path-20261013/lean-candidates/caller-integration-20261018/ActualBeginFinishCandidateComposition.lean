import PoseidonCompositionPartsG3Exact
import ActualBeginSelectedCanonical
import ActualFinishAlphaSelectedCanonical
import SelectedClaimGatherStable

/-! Candidate continuation on the exact returned begin/finish data. No point,
challenge or Poseidon branch-success contract is supplied independently.
Claim parser canonicality and source/model boundaries remain explicit. -/
set_option autoImplicit false
namespace AspisR1.ActualBeginFinishCandidateComposition
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CompositionPartsAfterValidation
open AspisR1.SemanticCompositionCoefficients
open AspisR1.PoseidonCompositionPartsG3Exact
open AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy
open scoped BigOperators
abbrev PublicQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev QM := field.QM31
abbrev ToSelected := AspisR1PublicPreparation.SemanticCallSelectedCanonical.toSelected
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev SelectedCanonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Statement := AspisR1TerminalDecoder.PublicBinding.Statement
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev selectedAlpha := AspisR1PublicPreparation.ActualFinishAlphaSelectedCanonical.selectedAlpha

def copyQMArray {n : Usize} (a : Array PublicQM n) : Array QM n :=
  ⟨a.val.map ToSelected, by simp [a.property]⟩

def copiedClaims (a : Array (Array PublicQM 29#usize) 3#usize) :
    Array (Array QM 29#usize) 3#usize :=
  ⟨a.val.map copyQMArray, by simp [a.property]⟩

theorem copiedClaims_cell (a : Array (Array PublicQM 29#usize) 3#usize)
    (p : Fin 3) (j : Fin 29) :
    ((copiedClaims a).val[p.val]'(by
      simpa [(copiedClaims a).property] using p.isLt)).val[j.val]'(by
        have hp : p.val < (copiedClaims a).val.length := by
          simpa [(copiedClaims a).property] using p.isLt
        simpa [((copiedClaims a).val[p.val]'hp).property] using j.isLt) =
    ToSelected ((a.val[p.val]'(by simpa [a.property] using p.isLt)).val[j.val]'(by
      have hp : p.val < a.val.length := by simpa [a.property] using p.isLt
      simpa [(a.val[p.val]'hp).property] using j.isLt)) := by
  simp only [copiedClaims, copyQMArray, List.getElem_map]

/-- Full candidate source result with its 29-coefficient mathematical model. -/
def ResultAt (s : Statement) (claims : Array QM 84#usize)
    (point : Array QM 10#usize) (lambda chi theta : QM) : Prop :=
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
            (AspisR1.CopyLinkWeightExact.modelVariant (copyVariant (copyFromStatement s).variant))).1 i

/-- The candidate continuation consumes the successful verifier's alpha and
begin challenges, and the actual terminal gather on its returned claims.
Canonicality of the 3x28 decoded claim cells is still a parser obligation.
This is not an assertion that the opaque finish boundary B.terminal is the
candidate continuation; that source instantiation remains separate. -/
theorem begin_finish_candidate_run
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Statement) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (hash : H) (c1 : Array U8 32#usize)
    (initial afterBegin : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (challenges : AspisR1PublicPreparation.r1_wire.Challenges)
    (obs : Option (AspisR1PublicPreparation.verifier.Phase → Result Unit))
    (out : AspisR1PublicPreparation.r1_semantic.Verified H)
    (hprep : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)
      hash c1 = .ok (.Ok initial))
    (hbegin : AspisR1PublicPreparation.r1_wire.begin D pre initial =
      .ok (.Ok challenges, afterBegin))
    (hfinish : AspisR1PublicPreparation.FinishModel.finish R B D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)
      pre afterBegin challenges obs = .ok (.Ok out))
    (hclaims : ∀ p : Fin 3, ∀ j : Fin 28,
      SelectedCanonical (ToSelected
        ((out.claims.val[p.val]'(by simpa [out.claims.property] using p.isLt)).val[
          j.val]'(by
            have hp : p.val < out.claims.val.length := by
              simpa [out.claims.property] using p.isLt
            simpa [(out.claims.val[p.val]'hp).property] using
              (show j.val < 29 by omega))))) :
    ∃ selected : Array QM 84#usize,
      array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
        pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO (copiedClaims out.claims) = .ok selected ∧
      ResultAt s selected (selectedAlpha out.alpha)
        (ToSelected challenges.lambda) (ToSelected challenges.chi)
        (ToSelected challenges.theta) := by
  obtain ⟨hlambda, hchi, htheta, hmu, heta, hzc⟩ :=
    AspisR1PublicPreparation.ActualBeginSelectedCanonical
      .begin_challenges_selected_canonical D pre initial afterBegin challenges hbegin
  have hpoint := AspisR1PublicPreparation.ActualFinishAlphaSelectedCanonical
    .selected_alpha_array_canonical_of_finish_success R B D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)
      pre afterBegin challenges obs out hfinish
  have hcopied : ∀ p : Fin 3, ∀ j : Fin 28,
      SelectedCanonical
        (((copiedClaims out.claims).val[p.val]'(by
          simpa [(copiedClaims out.claims).property] using p.isLt)).val[
            j.val]'(by
              have hp : p.val < (copiedClaims out.claims).val.length := by
                simpa [(copiedClaims out.claims).property] using p.isLt
              simpa [((copiedClaims out.claims).val[p.val]'hp).property] using
                (show j.val < 29 by omega))) := by
    intro p j
    rw [copiedClaims_cell out.claims p ⟨j.val, by omega⟩]
    exact hclaims p j
  obtain ⟨selected, hgather, hcells, hselected⟩ :=
    AspisR1SelectedMaskProbe.terminal_selected_gather_success
      (copiedClaims out.claims) hcopied
  refine ⟨selected, hgather, ?_⟩
  exact AspisR1.PoseidonCompositionPartsG3Exact.run_candidate_success
    (selectedAlpha out.alpha) s selected (ToSelected challenges.lambda)
    (ToSelected challenges.chi) (ToSelected challenges.theta)
    hpoint hselected hlambda hchi htheta D hash c1 initial hprep

#print axioms copiedClaims_cell
#print axioms begin_finish_candidate_run
end
end AspisR1.ActualBeginFinishCandidateComposition
