import CompositionPartsGatherStable
import SelectorRowSemantic
import SemanticPackedSixFamiliesActualPreparationClosed

set_option autoImplicit false
namespace AspisR1CompositionPartsPreparationPrelude
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedLoopModel
open AspisR1.ValueFamilyFieldTransport
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.SemanticPackedSixFamilies

/-- From canonical 84-cell claims and one canonical ten-factor point, the exact
four `composition_parts` gathers and boxed selector call succeed. The semantic
array is derived from the same successful public preparation. This is a
component prelude; the enclosing `composition_parts` caller/reachability proof
remains separate. -/
theorem actual_preparation_gather_and_semantic
    (claims : Array field.QM31 84#usize)
    (hclaims : ∀ j : Fin 84,
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (claims.val[j.val]'(by simpa [claims.property] using j.isLt)))
    (point : Array QM 10#usize) (hpoint : CanonicalArray point)
    (s : AspisR1TerminalDecoder.PublicBinding.Statement)
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (c1 : Array U8 32#usize)
    (outTranscript : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (hprep : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)
      hash c1 = Result.ok (.Ok outTranscript)) :
    ∃ (z succZ xor12Z : Array field.QM31 16#usize)
      (maskOnly : Array field.QM31 10#usize)
      (selectors : Selectors),
      array_from_fn_copy 16#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
        AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO claims = .ok z ∧
      array_from_fn_copy 16#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
        AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO claims = .ok succZ ∧
      array_from_fn_copy 16#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
        AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO claims = .ok xor12Z ∧
      array_from_fn_copy 10#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
        AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO claims = .ok maskOnly ∧
      (∀ i : Fin 16, z.val[i.val]'(by simpa [z.property] using i.isLt) =
        claims.val[i.val]'(by
          have hlen : claims.val.length = 84 := by simpa using claims.property
          omega)) ∧
      (∀ i : Fin 16, succZ.val[i.val]'(by simpa [succZ.property] using i.isLt) =
        claims.val[28 + i.val]'(by
          have hlen : claims.val.length = 84 := by simpa using claims.property
          omega)) ∧
      (∀ i : Fin 16, xor12Z.val[i.val]'(by simpa [xor12Z.property] using i.isLt) =
        claims.val[56 + i.val]'(by
          have hlen : claims.val.length = 84 := by simpa using claims.property
          omega)) ∧
      (∀ i : Fin 10, maskOnly.val[i.val]'(by simpa [maskOnly.property] using i.isLt) =
        claims.val[16 + i.val]'(by
          have hlen : claims.val.length = 84 := by simpa using claims.property
          omega)) ∧
      (∀ i : Fin 16, AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (z.val[i.val]'(by simpa [z.property] using i.isLt))) ∧
      (∀ i : Fin 16, AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (succZ.val[i.val]'(by simpa [succZ.property] using i.isLt))) ∧
      (∀ i : Fin 16, AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (xor12Z.val[i.val]'(by simpa [xor12Z.property] using i.isLt))) ∧
      (∀ i : Fin 10, AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (maskOnly.val[i.val]'(by simpa [maskOnly.property] using i.isLt))) ∧
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors ∧
      CanonicalArray selectors.high ∧ CanonicalArray selectors.low ∧
      (∀ row : Fin 1024,
        (AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high (row.val >>> 4) *
          AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low (row.val &&& 15) =
          AspisV8.SelectedSelectorExpansion.selectedSelector
            (AspisR1.SelectorAtPointModel.exactPoint point) row.val) ∧
        (AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high (row.val >>> 4) *
          AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low (row.val &&& 15) =
          AspisV8.SelectedSelectorExpansion.tensorProduct
            (AspisR1.SelectorAtPointModel.exactPoint point) 10 row.val)) ∧
      (∃ semanticOut,
        AspisR1SemanticPackedBoundedCandidate.pool_v1.pair_forest_semantic_terminal.semantic_packed
          (AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy.copyFromStatement s)
          { z := z, succ_z := succZ, xor12_z := xor12Z } selectors = .ok semanticOut ∧
        CanonicalArray semanticOut ∧
        ∀ j : Fin 24, f (decoded semanticOut j) =
          R0P.pack4 PackB (fun k => R0P.SemSource.scalarLaneAt
            (publicWide (AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy.copyFromStatement s))
            (AspisR1.ValueFamilyFieldTransport.mapOpenings f
              (exactOpenings ({ z := z, succ_z := succZ, xor12_z := xor12Z } : Openings)))
            (fun i => f (pointSelector point i)) (4*j.val+k.val))) := by
  obtain ⟨⟨z, hzrun, hzcell, hzcan⟩,
      ⟨succZ, hsuccrun, hsucccell, hsucccan⟩,
      ⟨xor12Z, hxorrun, hxorcell, hxorcan⟩⟩ :=
    first_three_gathers claims hclaims
  obtain ⟨maskOnly, hmaskrun, hmaskcell, hmaskcan⟩ :=
    mask_only_gather claims hclaims
  obtain ⟨selectors, hbox, hhigh, hlow, hrows⟩ :=
    AspisR1.SelectorRowSemantic.boxed_row_products point hpoint
  obtain ⟨semanticOut, hsemantic, hsemanticCan, hsemanticModel⟩ :=
    AspisR1.SemanticPackedSixFamiliesActualPreparation.actual_semantic_packed_of_preparation
      point selectors s { z := z, succ_z := succZ, xor12_z := xor12Z }
      hpoint hbox hzcan hsucccan hxorcan D hash c1 outTranscript hprep
  refine ⟨z, succZ, xor12Z, maskOnly, selectors, hzrun, hsuccrun,
    hxorrun, hmaskrun, hzcell, hsucccell, hxorcell, hmaskcell,
    hzcan, hsucccan, hxorcan, hmaskcan, hbox, hhigh, hlow, hrows, ?_⟩
  exact ⟨semanticOut, hsemantic, hsemanticCan, hsemanticModel⟩

#print axioms actual_preparation_gather_and_semantic
end
end AspisR1CompositionPartsPreparationPrelude
