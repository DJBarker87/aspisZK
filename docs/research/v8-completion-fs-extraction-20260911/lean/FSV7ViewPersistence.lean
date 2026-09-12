import FSV7ParentScript

/-! Previously issued parent hashes retain their values through later
chronological script execution. Reachable log consistency is a named invariant
with a producer, not a freely assumed equality of an independent hash view. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7ViewPersistence
open FSOracleExecution FSBoundedTranscript FSExposureOrder FSV7PrefixBridge
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths

theorem logged_view_preserved {A : Type} {n : Nat} (tape : Tape) (s : Oracle)
    (later : Script (List UInt8) FSBoundedTranscript.Block A n) (coherent : LogConsistent s)
    (input : RawHashInput) (seen : input ∈ oldLog s) :
    oldView (run tape later s).2 input = oldView s input := by
  obtain ⟨event, member, eq⟩ := List.mem_map.mp seen
  subst input
  have before := coherent event member
  have after := run_preserves_answer tape later s event.input event.answer before
  simp only [oldView, FSAuthenticationPrefixes.totalView208,
    FSAuthenticationPrefixes.view208, decode_encode, before, after]

theorem parent_congr (left right : RawHashInput → Digest208)
    (position : Nat) (current sibling : Digests)
    (same : ∀ input ∈ nodeCalls position current sibling, left input = right input) :
    parent left position current sibling = parent right position current sibling := by
  unfold parent
  congr 1
  funext side
  apply same
  fin_cases side
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- A successful functional pass depends only on its actual emitted calls.
No equality on unqueried/default-view inputs is needed. -/
theorem pass_view_congr {left right : RawHashInput → Digest208}
    {entries output : List Entry} {frontier remaining : List Digests}
    {trace : OrderedRawQueryLog}
    (accepted : Pass left entries frontier output remaining trace)
    (same : ∀ input ∈ trace, left input = right input) :
    Pass right entries frontier output remaining trace := by
  induction accepted with
  | nil frontier => exact Pass.nil frontier
  | @pair k current sibling rest output frontier remaining trace tail ih =>
    have parentSame := parent_congr left right (2*k) current sibling
      (fun input member => same input (List.mem_append_left _ member))
    rw [parentSame]
    exact Pass.pair k current sibling
      (ih (fun input member => same input (List.mem_append_right _ member)))
  | @single head sibling rest output frontier remaining trace unpaired tail ih =>
    have parentSame := parent_congr left right head.position head.digest sibling
      (fun input member => same input (List.mem_append_left _ member))
    rw [parentSame]
    exact Pass.single head sibling unpaired
      (ih (fun input member => same input (List.mem_append_right _ member)))

theorem pass_through_later {A : Type} {n : Nat} (tape : Tape) (s : Oracle)
    (later : Script (List UInt8) FSBoundedTranscript.Block A n) (coherent : LogConsistent s)
    {entries output : List Entry} {frontier remaining : List Digests}
    {trace : OrderedRawQueryLog}
    (accepted : Pass (oldView s) entries frontier output remaining trace)
    (included : TraceIncludedInLog trace (oldLog s)) :
    Pass (oldView (run tape later s).2) entries frontier output remaining trace := by
  apply pass_view_congr accepted
  intro input member
  exact (logged_view_preserved tape s later coherent input (included input member)).symm

#print logged_view_preserved
#print pass_through_later
#print axioms logged_view_preserved
#print axioms parent_congr
#print axioms pass_view_congr
#print axioms pass_through_later
end AspisV8Completion.FSV7ViewPersistence
