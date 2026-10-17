import TerminalValidateTransitionStepCarry
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisR1TerminalValidateTransitionCandidate.ExpectedAt
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
abbrev Usize := UScalar UScalarTy.Usize
abbrev M31 := field.M31
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic

/-- The exact row operand chosen by the validate-transition source branch,
with its iterator bookkeeping projected away. -/
def expectedAt (public1 : Public) (level carry : Usize) : Result (Array M31 8#usize) := do
  if level < carry then
    AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
  else
    let i ← public1.transition.live_snapshot.next_pair_index >>> level
    let i1 ← lift (i &&& 1#u64)
    if i1 = 0#u64 then
      AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
    else
      Array.index_usize public1.transition.live_snapshot.frontier level

private def resultMap {α β : Type} (r : Result α) (f : α → β) : Result β := do
  let x ← r
  ok (f x)

/-- The exact `expectedWithIter` helper is the mapped projected branch result. -/
theorem expectedWithIter_map (public1 : Public)
    (iter : AspisR1TerminalValidateTransitionCandidate.Range) (level carry : Usize) :
    AspisR1TerminalValidateTransitionCandidate.expectedWithIter public1 iter level carry =
      resultMap (expectedAt public1 level carry) (fun expected => (iter, expected)) := by
  by_cases h : level < carry <;>
    simp [resultMap, AspisR1TerminalValidateTransitionCandidate.expectedWithIter,
      expectedAt, h, bind_tc_ok]

/-- A successful exact loop operand identifies the projected source row result. -/
theorem expectedAt_of_expectedWithIter
    (public1 : Public) (iterAfter : AspisR1TerminalValidateTransitionCandidate.Range)
    (level carry : Usize) (expected : Array M31 8#usize)
    (h : AspisR1TerminalValidateTransitionCandidate.expectedWithIter
      public1 iterAfter level carry = .ok (iterAfter, expected)) :
    expectedAt public1 level carry = .ok expected := by
  rw [expectedWithIter_map] at h
  cases he : expectedAt public1 level carry with
  | ok row =>
      simp [resultMap, he] at h
      have hrow : row = expected := h
      exact congrArg Result.ok hrow
  | fail e => simp [resultMap, he] at h
  | div => simp [resultMap, he] at h

#print axioms expectedWithIter_map
#print axioms expectedAt_of_expectedWithIter
end AspisR1TerminalValidateTransitionCandidate.ExpectedAt
