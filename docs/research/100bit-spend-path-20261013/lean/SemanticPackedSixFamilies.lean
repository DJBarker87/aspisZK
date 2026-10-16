import SemanticPackedBoundedFactoring
import DigestPackedContribution
import SemanticPackedFamilyAssembly

/-! Actual complete semantic_packed caller, including all six families.
The independent outer digest-loop theorem remains an explicit premise. -/
set_option autoImplicit false
namespace AspisR1.SemanticPackedSixFamilies
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

def publicWide (public1 : Public) : R0P.Public Wide := SpendDataMap.mapPublic f (exactPublic public1)

theorem factored_eq (public1 : Public) (openings : Openings) (selectors : Selectors) :
    SemanticPackedBoundedFactoring.run public1 openings selectors =
      (do
        let first4 ← SemanticPackedPrefix.run public1 openings selectors
        let packed ← DigestPackedContribution.run first4 public1 openings selectors
        AspisR1ScalarSuffixCandidate.scalar_suffix packed public1 openings selectors) := by
  simp only [SemanticPackedBoundedFactoring.run, DigestPackedContribution.run, bind_assoc_eq]

attribute [local irreducible] R0P.scheduleFamily R0P.pathFamily R0P.valueFamily
  R0P.occupancyFamily R0P.digestFamily R0P.assetFamily R0P.pack4
  AspisR1.SelectorValueLaneModelComposition.pointSelector
  AspisR1.ValueLaneResidualList.selectList

theorem actual_semantic_packed_of_outer
    (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (openings : Openings)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z)
    (hxor : CanonicalArray openings.xor12_z)
    (ha : DigestFixedPrefix.DigestWordsCanonical public1.anchor)
    (hn : DigestFixedPrefix.DigestWordsCanonical public1.nullifier)
    (hc : DigestFixedPrefix.DigestWordsCanonical public1.change)
    (hr : ∀ recipient, public1.recipient = some recipient → DigestFixedPrefix.DigestWordsCanonical recipient)
    (hroot : DigestFixedPrefix.DigestWordsCanonical public1.transition.candidate_afterstate.next_root)
    (hfrontier : ∀ j : Fin 20, DigestFixedPrefix.DigestWordsCanonical
      (public1.transition.candidate_afterstate.next_frontier.val[j.val]'(by
        simpa [public1.transition.candidate_afterstate.next_frontier.property] using j.isLt)))
    (hasset : public1.asset_id.val < AspisR1.TerminalLiftM31Exact.P)
    (hamount : (AspisR1.ScalarSuffixExecution.amountValue public1).val < AspisR1.TerminalLiftM31Exact.P)
    (houter : DigestWrapperComposition.OuterSound point selectors public1 openings) :
    ∃ out,
      AspisR1SemanticPackedBoundedCandidate.pool_v1.pair_forest_semantic_terminal.semantic_packed
        public1 openings selectors = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24, f (decoded out j) =
        R0P.pack4 PackB (fun k => R0P.SemSource.scalarLaneAt (publicWide public1)
          (mapOpenings f (exactOpenings openings)) (fun i => f (pointSelector point i))
          (4*j.val+k.val)) := by
  obtain ⟨first4, h4, hc4, hv4⟩ := SemanticPackedPrefix.source_success point selectors
    public1 openings (publicWide public1) hpoint hbox hz hsucc hxor (by rfl)
  obtain ⟨packed, hp, hcp, hvp⟩ := DigestPackedContribution.actual_digest_contribution point selectors
    first4 public1 openings hpoint hbox hc4 hz ha hn hc hr hroot hfrontier houter
  obtain ⟨out, ho, hco, hvo⟩ := ScalarSuffixPacking.actual_scalar_suffix point selectors
    packed public1 openings (publicWide public1) hpoint hbox hcp hz hasset hamount
      (by rfl) (by rfl) (by rfl)
  refine ⟨out, ?_, hco, ?_⟩
  · rw [SemanticPackedBoundedFactoring.whole_caller_eq_factored, factored_eq]
    rw [h4]
    simp only [bind_tc_ok]
    rw [hp]
    simp only [bind_tc_ok]
    exact ho
  · intro j
    rw [hvo j, hvp j, hv4 j]
    unfold SemanticPackedPrefix.model SemanticPackedPrefix.familyContribution
    exact SemanticPackedFamilyAssembly.packed_family_contributions PackB (publicWide public1)
      (mapOpenings f (exactOpenings openings)) (fun i => f (pointSelector point i)) j.val

#print axioms factored_eq
#print axioms actual_semantic_packed_of_outer
end
end AspisR1.SemanticPackedSixFamilies
