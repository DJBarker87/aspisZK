import SemanticPackedSixFamilies
import TerminalDigestPublicLoopFuel

/-! Discharge the last outer-loop premise of the complete six-family source
theorem. Public bounds are on that same source SemanticPublic. -/
set_option autoImplicit false
namespace AspisR1.SemanticPackedOuterClosed
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

theorem outer_sound (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (openings : Openings)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hz : CanonicalArray openings.z)
    (hsnapshot : ∀ j : Fin 20, DigestFixedPrefix.DigestWordsCanonical
      (public1.transition.live_snapshot.frontier.val[j.val]'(by
        simpa [public1.transition.live_snapshot.frontier.property] using j.isLt))) :
    DigestWrapperComposition.OuterSound point selectors public1 openings := by
  intro initial hinitial
  obtain ⟨middle, hm, hcm, hvm⟩ :=
    AspisR1TerminalDigestPublicLoop.Fuel.public_loop_success public1 point selectors openings
      initial rfl hpoint hbox hz hsnapshot hinitial
  exact ⟨middle, hm, hcm, hvm⟩

/-- Complete actual source execution and all24 retained lane equations.
No outer-loop, branch, family or intermediate operation success is assumed. -/
theorem actual_semantic_packed
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
    (hsnapshot : ∀ j : Fin 20, DigestFixedPrefix.DigestWordsCanonical
      (public1.transition.live_snapshot.frontier.val[j.val]'(by
        simpa [public1.transition.live_snapshot.frontier.property] using j.isLt)))
    (hroot : DigestFixedPrefix.DigestWordsCanonical public1.transition.candidate_afterstate.next_root)
    (hfrontier : ∀ j : Fin 20, DigestFixedPrefix.DigestWordsCanonical
      (public1.transition.candidate_afterstate.next_frontier.val[j.val]'(by
        simpa [public1.transition.candidate_afterstate.next_frontier.property] using j.isLt)))
    (hasset : public1.asset_id.val < AspisR1.TerminalLiftM31Exact.P)
    (hamount : (AspisR1.ScalarSuffixExecution.amountValue public1).val < AspisR1.TerminalLiftM31Exact.P) :
    ∃ out,
      AspisR1SemanticPackedBoundedCandidate.pool_v1.pair_forest_semantic_terminal.semantic_packed
        public1 openings selectors = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24, f (decoded out j) =
        R0P.pack4 PackB (fun k => R0P.SemSource.scalarLaneAt (SemanticPackedSixFamilies.publicWide public1)
          (mapOpenings f (exactOpenings openings)) (fun i => f (pointSelector point i))
          (4*j.val+k.val)) := by
  exact SemanticPackedSixFamilies.actual_semantic_packed_of_outer point selectors public1 openings
    hpoint hbox hz hsucc hxor ha hn hc hr hroot hfrontier hasset hamount
    (outer_sound point selectors public1 openings hpoint hbox hz hsnapshot)

#print axioms outer_sound
#print axioms actual_semantic_packed
end
end AspisR1.SemanticPackedOuterClosed
