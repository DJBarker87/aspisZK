import PCD_Checked
import PCD_FrontierValue
import PCD_EmptyRoots
import PCD_LaneLoopIndex
import PCD_LaneResult
import PCD_State
set_option autoImplicit false
namespace PCD_LaneModel
open Aeneas Aeneas.Std PCD PCD_LaneRef PCD_LaneLoop

def levelWord (level : Nat) : U32 := ⟨BitVec.ofNat 32 level⟩

def tests (after : After) (level : Nat) : Bool :=
  if h : level < 20 then
    PCD_FrontierValue.test after.next_pair_index (levelWord level)
      (after.next_frontier.val[level]'(by rw [after.next_frontier.property]; exact h))
      (PCD_EmptyRoots.roots.val[level]'(by rw [PCD_EmptyRoots.roots.property]; exact h))
  else false

/-- Fixed input interpretation; no Ops, child-result, successful endpoint or
freely chosen per-level test is an argument of this definition. -/
def source (lane : Lane) (after : After) : Exit Lane :=
  PCD_LaneResult.source lane after
    (decide (U64.checked_add lane.tree.next_leaf_index 1#u64 = some after.next_pair_index))
    (tests after)

noncomputable def specification (lane : Lane) (after : After) : Exit Lane := by
  classical
  exact if U64.checked_add lane.tree.next_leaf_index 1#u64 = some after.next_pair_index then
    if good (tests after) 0 20 then .ok (PCD_LaneValue.candidate lane after)
    else .error (.custom 0x41532003)
  else .error (.custom 0x41532003)

/-- Complete model Result: checked-add failure, first frontier rejection and
successful full record, on all own typed inputs. Native segment certificates
and exact source association are recorded separately, never assumed as Ops. -/
theorem result (lane : Lane) (after : After) :
    source lane after = specification lane after := by
  classical
  unfold source PCD_LaneResult.source specification
  by_cases checked : U64.checked_add lane.tree.next_leaf_index 1#u64 = some after.next_pair_index
  · simp only [checked, ↓reduceIte, decide_true]
    cases h : scan (tests after) 0 20 with
    | done out =>
      have idx := done_index (tests after) 0 20 out h
      have all : good (tests after) 0 20 := (scan_done_iff (tests after) 0 20).1 (by simpa [idx] using h)
      simp only [h, all, ↓reduceIte]
    | rejected whereFailed =>
      have bad := rejected_not_good (tests after) 0 20 whereFailed h
      simp only [h, bad, ↓reduceIte]
  · simp only [checked, ↓reduceIte, decide_false, Bool.false_eq_true]

/-- The row has no mutable input or runtime effects. Its modeled frame is
exact on any state; native modifies() checks are required for each segment. -/
theorem result_state_effects {State : Type} (lane : Lane) (after : After) (state : State) :
    (source lane after, state, ([] : List PCD.Event)) =
      (specification lane after, state, []) := by
  rw [result]

#print axioms result
#print axioms result_state_effects
end PCD_LaneModel
