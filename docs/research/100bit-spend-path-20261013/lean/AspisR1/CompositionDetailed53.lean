import AspisR1.CompositionPartsAfterValidationSource
import AspisR1.PreparedCopyComposition53
import AspisR1.PoseidonCallable53

/-! Same-input caller composition. The Poseidon callable contract is explicit
until its separate actual source/family bridge is installed. The caller itself
selects H1, index and variant; those are no longer independently supplied model
values. Entry guards and whole terminal/verifier reachability remain separate. -/
set_option autoImplicit false
namespace AspisR1.CompositionDetailed53
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

/-- The complete source continue branch on the actual gathers and source H1,
with one still-explicit callable contract for Poseidon. -/
theorem run_success
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
      run PoseidonCallable53.source (copyFromStatement s) claims point lambda chi theta =
        .ok (.Ok (out, openings.z, maskOnly, q, helper, active)) ∧
      CanonicalQM out ∧ CanonicalQM q ∧ CanonicalQM active ∧
      decode active = R0P.copyActiveLiteral (AspisR1.CopyEndpointExact.modelSelectors selectors) ∧
      decode out = ∑ i : Fin 29, decode theta ^ i.val *
        lanesFromModels ((PoseidonCallable53.model point) openings selectors)
          (semanticLane24 (copyFromStatement s) openings point)
          (R0P.copyEvaluateWithSelectors
            (AspisR1.CopyEndpointExact.decodedCells openings.z) (decode helper)
            (AspisR1.CopyEndpointExact.modelSelectors selectors) (decode lambda) (decode chi)
            (copyFromStatement s).transition.live_snapshot.next_pair_index.val
            (AspisR1.CopyLinkWeightExact.modelVariant (copyVariant (copyFromStatement s).variant))).1 i := by
  obtain ⟨⟨z,hz,hzcells,hzcan⟩,⟨succZ,hsucc,hsucccells,hsucccan⟩,
    ⟨xorZ,hxor,hxorcells,hxorcan⟩⟩ := first_three_gathers claims hclaims
  obtain ⟨maskOnly,hmask,hmaskcells,hmaskcan⟩ := mask_only_gather claims hclaims
  obtain ⟨selectors,hbox,hhigh,hlow,hrows⟩ :=
    AspisR1.SelectorRowSemantic.boxed_row_products point hpoint
  let openings : Openings := { z := z, succ_z := succZ, xor12_z := xorZ }
  obtain ⟨poseidon,hposeidonRun,hposeidonCan,hposeidonValue⟩ :=
    PoseidonCallable53.source_success openings point selectors hpoint hzcan hsucccan hxorcan hbox
  obtain ⟨helper,hhelperRun,hhelperCell,hhelperCan⟩ :=
    selected_claim_success claims 0#usize 26#usize (by decide) (by decide) hclaims
  obtain ⟨selectors',semantic,copy,out,q,hbox',hsemantic,hcopy,htail,
    houtCan,hqCan,hactiveCan,hactiveValue,hvalue⟩ :=
    AspisR1.PreparedCopyComposition53.components_and_tail
      point s openings poseidon ((PoseidonCallable53.model point) openings selectors) claims maskOnly
      helper lambda chi theta (copyFromStatement s).transition.live_snapshot.next_pair_index
      (copyVariant (copyFromStatement s).variant) hpoint hzcan hsucccan hxorcan
      hposeidonCan hposeidonValue hclaims hhelperCan hlambda hchi htheta
      D hash c1 outTranscript hprep
  have heq : selectors' = selectors := by
    rw [hbox] at hbox'
    exact (Result.ok.inj hbox').symm
  subst selectors'
  refine ⟨openings,selectors,maskOnly,helper,out,q,copy.active,
    hzcells,hsucccells,hxorcells,hbox,hhelperRun,?_,houtCan,hqCan,hactiveCan,hactiveValue,hvalue⟩
  dsimp only [openings] at hposeidonRun hsemantic hcopy htail
  unfold run
  simp only [hz, bind_tc_ok, hsucc, hxor, hmask, hbox, hposeidonRun, hsemantic,
    selected_h1_column_ok, hhelperRun, copyVariantSource_success, hcopy]
  exact htail

#print axioms run_success
end
end AspisR1.CompositionDetailed53
