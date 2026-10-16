import DigestWrapperComposition
import DigestFamilyFieldTransport
import ScalarSuffixPacking

set_option autoImplicit false
namespace AspisR1.DigestPackedContribution
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
abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev exactPublic := AspisR1.SemanticPublicModel.exactPublic
abbrev digestDecoded := AspisR1.DigestFixedBinding.decoded
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

theorem decoded_array_list (values : Array QM 8#usize) :
    values.val.map decode = List.ofFn (digestDecoded values) := by
  have h8 : (8#usize).val = 8 := by scalar_tac
  apply List.ext_getElem
  · simp only [List.length_map, List.length_ofFn, values.property, h8]
  · intro n hn hm
    have hn8 : n < 8 := by simpa only [List.length_map, values.property, h8] using hn
    simp only [List.getElem_map, List.getElem_ofFn, digestDecoded,
      AspisR1.DigestFixedBinding.decoded,
      AspisR1TerminalDigestBindingCandidate.LoopExact.cellAt, dif_pos hn8]

theorem mapped_digest_list (values : Array QM 8#usize) (public1 : Public)
    (openings : Openings) (point : Array QM 10#usize)
    (hvalues : digestDecoded values = R0P.publicDigestLanes (exactPublic public1)
      (exactOpenings openings) (pointSelector point)) :
    List.ofFn (arrayVector values) =
      (R0P.digestFamily (K := Wide)).residuals (SpendDataMap.mapPublic f (exactPublic public1))
        (mapOpenings f (exactOpenings openings)) (fun i => f (pointSelector point i)) := by
  have hbase : values.val.map decode =
      (R0P.digestFamily (K := AspisV8R15.ExactTowerBase.QM31Exact)).residuals
        (exactPublic public1) (exactOpenings openings) (pointSelector point) := by
    rw [decoded_array_list, hvalues]
    rfl
  exact (AspisR1.ScalarSuffixPacking.array_mapped_list values).trans
    ((congrArg (List.map f) hbase).trans
      (DigestFamilyFieldTransport.map_family f (exactPublic public1)
        (exactOpenings openings) (pointSelector point)))

def run (packed : Array QM 24#usize) (public1 : Public) (openings : Openings)
    (selectors : Selectors) : Result (Array QM 24#usize) := do
  let values ← DigestWrapperComposition.wrapper public1 openings selectors
  AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
    packed 84#usize values

attribute [local irreducible] R0P.digestFamily R0P.pack4
  AspisR1.SelectorValueLaneModelComposition.pointSelector
  AspisR1.ValueLaneResidualList.selectList

/-- Actual digest call and slot84 packing, with the outer-loop obligation
explicit until its independent source proof instantiates it. -/
theorem actual_digest_contribution (point : Array QM 10#usize) (selectors : Selectors)
    (packed : Array QM 24#usize) (public1 : Public) (openings : Openings)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hpacked : CanonicalArray packed) (hz : CanonicalArray openings.z)
    (ha : DigestFixedPrefix.DigestWordsCanonical public1.anchor)
    (hn : DigestFixedPrefix.DigestWordsCanonical public1.nullifier)
    (hc : DigestFixedPrefix.DigestWordsCanonical public1.change)
    (hr : ∀ recipient, public1.recipient = some recipient → DigestFixedPrefix.DigestWordsCanonical recipient)
    (hroot : DigestFixedPrefix.DigestWordsCanonical public1.transition.candidate_afterstate.next_root)
    (hfrontier : ∀ j : Fin 20, DigestFixedPrefix.DigestWordsCanonical
      (public1.transition.candidate_afterstate.next_frontier.val[j.val]'(by
        simpa [public1.transition.candidate_afterstate.next_frontier.property] using j.isLt)))
    (houter : DigestWrapperComposition.OuterSound point selectors public1 openings) :
    ∃ out, run packed public1 openings selectors = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24, f (decoded out j) = f (decoded packed j) +
        R0P.pack4 PackB (fun k : Fin 4 => selectList 84
          ((R0P.digestFamily (K := Wide)).residuals
            (SpendDataMap.mapPublic f (exactPublic public1))
            (mapOpenings f (exactOpenings openings)) (fun i => f (pointSelector point i)))
          (4*j.val+k.val)) := by
  obtain ⟨values, hvalues, hcValues, hvValues⟩ :=
    DigestWrapperComposition.source_success_of_outer point selectors public1 openings
      hpoint hbox hz ha hn hc hr hroot hfrontier houter
  have hresiduals := mapped_digest_list values public1 openings point hvValues
  obtain ⟨out, hpack, hcOut, hvOut⟩ :=
    AspisR1.PreweightedListSemantic.add_preweighted_residual_list
      packed 84#usize values _ (by scalar_tac) (by scalar_tac) hpacked hcValues hresiduals
  refine ⟨out, ?_, hcOut, ?_⟩
  · unfold run
    rw [hvalues]
    simp only [bind_tc_ok]
    exact hpack
  · have hstart : (84#usize).val = 84 := by scalar_tac
    rw [hstart] at hvOut
    exact hvOut

#print axioms decoded_array_list
#print axioms mapped_digest_list
#print axioms actual_digest_contribution
end
end AspisR1.DigestPackedContribution
