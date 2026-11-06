import NKF_LaneTrace
set_option autoImplicit false
noncomputable section
namespace NKF_LaneFactor
open Aeneas Aeneas.Std Result
abbrev Node := NKF_LaneTrace.Node
abbrev Frontier := NKF_LaneTrace.Frontier
abbrev Reply := NKF_LaneTrace.Reply
attribute [local instance] Classical.propDecidable
/-- Factored replacement for K064's combined shape. Each component still
needs its own native association; these are model laws, not native credit. -/
def guard (empty node : Node) (occupied : Bool) : Reply :=
 if occupied = false ∧ node ≠ empty then .Err .InvalidAccountData else .Ok ()

theorem success_step {F : Type} (empty node : Node) (occupied : Bool)
 (before : Frontier) (level : Fin 20) :
 NKF_LaneTrace.iteration empty occupied before level (.Ok node : core.result.Result Node F)=
 (guard empty node occupied,NJD_LaneStep.write before level node) := by
 by_cases h : occupied=false ∧ node≠empty
 · simp only [NKF_LaneTrace.iteration,NJD_LaneStep.step,guard,if_pos h]
 · simp only [NKF_LaneTrace.iteration,NJD_LaneStep.step,guard,if_neg h]

theorem selected {F : Type} (empty node : Node) (occupied : Bool)
 (before : Frontier) (level : Fin 20) (word : Fin 8) :
 (NKF_LaneTrace.iteration empty occupied before level (.Ok node : core.result.Result Node F)).2 level word=node word := by
 rw [success_step]
 exact congrFun (NJD_LaneStep.written before level node) word

theorem coordinate {F : Type} (empty : Node) (occupied : Bool)
 (before : Frontier) (level other : Fin 20) (word : Fin 8)
 (raw : core.result.Result Node F) :
 (NKF_LaneTrace.iteration empty occupied before level raw).2 other word=
 match raw with
 | .Err _ => before other word
 | .Ok node => if other=level then node word else before other word := by
 cases raw with
 | Err e => rfl
 | Ok node => rw [success_step]; simp only [NJD_LaneStep.write,ite_apply]

/-- Full node comparison follows from a single arbitrary word; no large
empty-root table is reduced. -/
theorem node_eq (a b : Node) (windows : ∀ word : Fin 8, a word=b word) : a=b := by
 funext word; exact windows word

theorem accepted_guard (empty node : Node) (occupied : Bool) :
 guard empty node occupied=.Ok () ↔ occupied=true ∨ node=empty := by
 cases occupied <;> simp [guard]

/-- Arbitrary offset geometry of the frozen 48+32*level window. -/
theorem window_bounds (level i : Nat) (hl : level<20) (hi : i<32) :
 48+32*level+i<688 ∧ 48+32*level+32≤688 := by omega

theorem distinct_windows (a b i j : Nat) (hi : i<32) (hj : j<32)
 (different : a≠b) : 48+32*a+i≠48+32*b+j := by omega

#print axioms success_step
#print axioms selected
#print axioms coordinate
#print axioms node_eq
#print axioms accepted_guard
#print axioms window_bounds
#print axioms distinct_windows
end NKF_LaneFactor
