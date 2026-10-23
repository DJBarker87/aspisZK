import AspisR1.CompositionPartsAfterValidationExact
import R1Z.ProverCommitPoseidonCallable55

/-! Same-input caller composition. The Poseidon callable contract is explicit
until its separate actual source/family bridge is installed. The caller itself
selects H1, index and variant; those are no longer independently supplied model
values. Entry guards and whole terminal/verifier reachability remain separate. -/
set_option autoImplicit false
namespace R1Z.ProverCommitComposition55
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
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Statement := AspisR1TerminalDecoder.PublicBinding.Statement
abbrev Semantic := Array QM 24#usize

theorem source_success
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
      run ProverCommitPoseidonCallable55.run (copyFromStatement s) claims point lambda chi theta =
        .ok (.Ok (out, openings.z, maskOnly, q, helper, active)) ∧
      CanonicalQM out ∧ CanonicalQM q ∧ CanonicalQM active ∧
      decode out = ∑ i : Fin 29, decode theta ^ i.val *
        lanesFromModels (ProverCommitPoseidonCallable55.model point openings)
          (semanticLane24 (copyFromStatement s) openings point)
          (R0P.copyEvaluateWithSelectors
            (AspisR1.CopyEndpointExact.decodedCells openings.z) (decode helper)
            (AspisR1.CopyEndpointExact.modelSelectors selectors) (decode lambda) (decode chi)
            (copyFromStatement s).transition.live_snapshot.next_pair_index.val
            (AspisR1.CopyLinkWeightExact.modelVariant (copyVariant (copyFromStatement s).variant))).1 i := by
  apply AspisR1.CompositionPartsAfterValidationExact.run_success_of_poseidon_contract
    ProverCommitPoseidonCallable55.run (fun o _ => ProverCommitPoseidonCallable55.model point o)
    point s claims lambda chi theta hpoint hclaims hlambda hchi htheta
    ?_ D hash c1 outTranscript hprep
  intro openings selectors hbox hz hs hx
  exact ProverCommitPoseidonCallable55.callable openings point selectors hpoint hz hs hx hbox

#print axioms source_success
end
end R1Z.ProverCommitComposition55
