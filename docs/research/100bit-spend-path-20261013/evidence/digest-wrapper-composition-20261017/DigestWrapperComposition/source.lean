import DigestWrapperBoundedSource
import DigestFixedPrefixR0P
import DigestWrapperSuffixR0P

/-! Complete bounded-wrapper composition. The outer-loop premise is explicit
and must be discharged by the independent twenty-level source execution proof. -/
set_option autoImplicit false
namespace AspisR1.DigestWrapperComposition
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.LoopExact
open AspisR1.DigestFixedBinding
open AspisR1.DigestFixedPrefix
open AspisR1.DigestFixedPrefix.R0PBridge
abbrev Snapshot := pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev wrapper := AspisR1DigestWrapperBoundedCandidate.pool_v1.pair_forest_semantic_terminal.public_digest_lanes
abbrev outer := AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop

def withSnapshot (public1 : Public) (source : Snapshot) : Public :=
  { public1 with transition := { public1.transition with live_snapshot := source } }

def factored (public1 : Public) (openings : Openings) (selectors : Selectors) :
    Result (Array QM 8#usize) := do
  let initial ← Source.exactPrefix public1 openings selectors
  let (middle, source) ← outer { start := 0#usize, «end» := 20#usize }
    openings.z selectors initial public1.transition.live_snapshot
  AspisR1.DigestWrapperSuffix.run middle openings.z selectors (withSnapshot public1 source)

private theorem result_right_identity {α : Type} (x : Result α) :
    (do let y ← x; Result.ok y) = x := by
  cases x <;> rfl

/-- The candidate's whole wrapper is the original-source prefix, the actual
outer loop and the proven bounded-source suffix, preserving Result errors. -/
theorem wrapper_eq_factored (public1 : Public) (openings : Openings) (selectors : Selectors) :
    wrapper public1 openings selectors = factored public1 openings selectors := by
  cases hrec : public1.recipient <;>
    simp only [wrapper, hrec,
    AspisR1DigestWrapperBoundedCandidate.pool_v1.pair_forest_semantic_terminal.public_digest_lanes,
    factored, Source.exactPrefix, AspisR1.DigestWrapperSuffix.run, bindBlock,
    withSnapshot, bind_assoc_eq, bind_tc_ok, result_right_identity]
  all_goals rfl

def OuterSound (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (openings : Openings) : Prop :=
  ∀ initial : Array QM 8#usize, CanonicalArray initial →
    ∃ middle, outer { start := 0#usize, «end» := 20#usize }
      openings.z selectors initial public1.transition.live_snapshot =
        .ok (middle, public1.transition.live_snapshot) ∧
      CanonicalArray middle ∧
      decoded middle = AspisR1TerminalDigestPublicLoop.Model.frontierPrefix
        (SemanticPublicModel.exactPublic public1) (exactOpenings openings)
        (pointSelector point) 20 (decoded initial)

attribute [local irreducible] R0P.digestAddBinding
  AspisR1.SelectorValueLaneModelComposition.pointSelector

theorem source_success_of_outer (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (openings : Openings)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hopened : CanonicalArray openings.z)
    (ha : DigestWordsCanonical public1.anchor)
    (hn : DigestWordsCanonical public1.nullifier)
    (hc : DigestWordsCanonical public1.change)
    (hr : ∀ recipient, public1.recipient = some recipient → DigestWordsCanonical recipient)
    (hroot : DigestWordsCanonical public1.transition.candidate_afterstate.next_root)
    (hfrontier : ∀ j : Fin 20, DigestWordsCanonical
      (public1.transition.candidate_afterstate.next_frontier.val[j.val]'(by
        simpa [public1.transition.candidate_afterstate.next_frontier.property] using j.isLt)))
    (houter : OuterSound point selectors public1 openings) :
    ∃ out, wrapper public1 openings selectors = .ok out ∧ CanonicalArray out ∧
      decoded out = R0P.publicDigestLanes (SemanticPublicModel.exactPublic public1)
        (exactOpenings openings) (pointSelector point) := by
  obtain ⟨initial, hi, hci, hvi⟩ := exactPrefix_success point selectors public1 openings
    hpoint hbox hopened ha hn hc hr
  obtain ⟨middle, hm, hcm, hvm⟩ := houter initial hci
  obtain ⟨out, ho, hco, hvo⟩ :=
    AspisR1.DigestWrapperSuffix.R0PBridge.source_success_r0p point selectors middle openings public1
      hpoint hbox hcm hopened hroot hfrontier
  refine ⟨out, ?_, hco, ?_⟩
  · rw [wrapper_eq_factored]
    unfold factored
    rw [hi]
    simp only [bind_tc_ok]
    rw [hm]
    simp only [bind_tc_ok]
    change AspisR1.DigestWrapperSuffix.run middle openings.z selectors public1 = .ok out
    exact ho
  · rw [hvo, hvm, hvi]
    exact (DigestModelDecomposition.complete_decomposition
      (SemanticPublicModel.exactPublic public1) (exactOpenings openings) (pointSelector point)).symm

#print axioms wrapper_eq_factored
#print axioms source_success_of_outer
end
end AspisR1.DigestWrapperComposition
