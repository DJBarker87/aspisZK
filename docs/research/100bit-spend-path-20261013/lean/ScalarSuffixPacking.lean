import ScalarSuffixExecution
import SemanticPublicModel
import AssetFamilyFieldTransport
import PreweightedListSemantic

/-! Complete actual scalar suffix and its retained asset-family contribution
in slots92/93, using the common exact public interpretation. -/
set_option autoImplicit false
namespace AspisR1.ScalarSuffixPacking
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneSourceVector
open AspisR1.ValueLaneResidualList
open AspisR1.ValueFamilyFieldTransport
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev exactOpenings := AspisR1.ScalarSuffixExecution.exactOpenings
abbrev pointSelector := AspisR1.ScalarSuffixExecution.pointSelector
abbrev exactPublic := AspisR1.SemanticPublicModel.exactPublic
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

theorem family_literal {K : Type} [Field K] (pub : R0P.Public K)
    (o : R0P.Openings K) (sel : R0P.Sel K) :
    (R0P.assetFamily (K := K)).residuals pub o sel =
      R0P.assetScalarLanes pub.variant pub.withdrawalAmount.isSome
        (sel 44 * (o.z 1 - pub.assetId))
        (sel 508 * (o.z 1 - pub.assetId))
        (sel 460 * (o.z 1 - pub.assetId))
        (sel 1010 * (o.z 10 - pub.withdrawalAmount.getD 0)) := by
  simp only [R0P.assetFamily,
    show (2*16+12 : Fin 1024) = 44 from by decide,
    show (31*16+12 : Fin 1024) = 508 from by decide,
    show (28*16+12 : Fin 1024) = 460 from by decide,
    show (16*63+2 : Fin 1024) = 1010 from by decide]

theorem array_mapped_list {N : Usize} (values : Array QM N) :
    List.ofFn (arrayVector values) = (values.val.map decode).map f := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, values.property]
  · intro n hn hm
    simp only [List.getElem_ofFn, List.getElem_map, arrayVector]

theorem suffix_eq_values (packed : Array QM 24#usize) (public1 : Public)
    (openings : Openings) (selectors : Selectors) :
    AspisR1ScalarSuffixCandidate.scalar_suffix packed public1 openings selectors =
      (do
        let values ← AspisR1ScalarSuffixCandidate.scalar_values public1 openings selectors
        AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted packed 92#usize values) := by
  simp only [AspisR1ScalarSuffixCandidate.scalar_suffix, AspisR1ScalarSuffixCandidate.scalar_values,
    bind_assoc, bind_tc_ok]

attribute [local irreducible] AspisR1.SelectorValueLaneModelComposition.pointSelector R0P.assetScalarLanes R0P.assetFamily R0P.pack4
  AspisR1.ValueLaneResidualList.selectList AspisR1.SemanticPublicModel.exactPublic

theorem actual_scalar_suffix (point : Array QM 10#usize) (selectors : Selectors)
    (packed : Array QM 24#usize) (public1 : Public) (openings : Openings) (pub : R0P.Public Wide)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hp : CanonicalArray packed) (hz : CanonicalArray openings.z)
    (hasset : public1.asset_id.val < AspisR1.TerminalLiftM31Exact.P)
    (hamount : (AspisR1.ScalarSuffixExecution.amountValue public1).val < AspisR1.TerminalLiftM31Exact.P)
    (hv : pub.variant = (exactPublic public1).variant)
    (ha : pub.assetId = f (exactPublic public1).assetId)
    (hw : pub.withdrawalAmount = (exactPublic public1).withdrawalAmount.map f) :
    ∃ out, AspisR1ScalarSuffixCandidate.scalar_suffix packed public1 openings selectors = .ok out ∧
      CanonicalArray out ∧ ∀ j : Fin 24,
      f (decoded out j) = f (decoded packed j) +
        R0P.pack4 PackB (fun k : Fin 4 => selectList 92
          ((R0P.assetFamily (K := Wide)).residuals pub
            (mapOpenings f (exactOpenings openings)) (fun i => f (pointSelector point i)))
          (4*j.val+k.val)) := by
  obtain ⟨values, hvalues, hcValues, hvValues⟩ := AspisR1.ScalarSuffixExecution.source_values
    point selectors public1 openings hpoint hbox hz hasset hamount
  have hfamily : values.val.map decode =
      (R0P.assetFamily (K := AspisV8R15.ExactTowerBase.QM31Exact)).residuals
        (exactPublic public1) (exactOpenings openings) (pointSelector point) := by
    rw [family_literal]
    simpa only [exactPublic, AspisR1.SemanticPublicModel.exactPublic,
      AspisR1.ScalarSuffixExecution.exactAmount, AspisR1.ScalarSuffixExecution.modelVariant] using hvValues
  have hwide := AspisR1.AssetFamilyFieldTransport.map_family f (exactPublic public1) pub
    (exactOpenings openings) (pointSelector point) hv ha hw
  have hresiduals := (array_mapped_list values).trans ((congrArg (List.map f) hfamily).trans hwide)
  obtain ⟨out, hpack, hcOut, hvOut⟩ := AspisR1.PreweightedListSemantic.add_preweighted_residual_list
    packed 92#usize values _ (by scalar_tac) (by scalar_tac) hp hcValues hresiduals
  refine ⟨out, ?_, hcOut, ?_⟩
  · rw [suffix_eq_values]
    simp only [hvalues, bind_tc_ok, hpack]
  · have hstart : (92#usize).val = 92 := by scalar_tac
    rw [hstart] at hvOut
    exact hvOut

#print axioms family_literal
#print axioms array_mapped_list
#print axioms suffix_eq_values
#print axioms actual_scalar_suffix
end
end AspisR1.ScalarSuffixPacking
