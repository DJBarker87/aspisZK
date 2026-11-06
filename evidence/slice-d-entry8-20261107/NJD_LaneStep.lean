import NJD_Trace
set_option autoImplicit false
noncomputable section
namespace NJD_LaneStep
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Node := Fin 8 → U32
abbrev Reply := core.result.Result Unit PE

/-- One digest-call continuation, including the assignment BEFORE a later
empty-subtree rejection. Native packet: NJD_lane.patch, K018/K019. -/
def step (empty : Node) (occupied : Bool) (old : Node)
    (decoded : core.result.Result Node PE) : Reply × Node := by
  classical
  exact match decoded with
  | .Err e => (.Err e,old)
  | .Ok value =>
    if occupied = false ∧ value ≠ empty then (.Err .InvalidAccountData,value)
    else (.Ok (),value)

/-- Transcription of the native node-coordinate assertion; no full-frontier
frame or adopted op50 endpoint is included. Native index is arbitrary <8. -/
def cut (canonical occupied sameEmpty : Bool) (before words after : Node)
    (returned : Reply) (pointer loggedPointer length calls : Nat)
    (index : Fin 8) (loggedIndex : Nat) (loggedWord : U32) : Prop :=
  (match returned with | .Ok _ => true | .Err _ => false) =
      (canonical && (occupied || sameEmpty)) ∧
  (returned = .Ok () ∨ returned = .Err .InvalidAccountData) ∧
  after index = (if canonical then words index else before index) ∧
  loggedPointer = pointer ∧ length = 32 ∧ calls = 1 ∧
  loggedIndex = index.val ∧ loggedWord = words index

theorem decode_error (empty old : Node) (occupied : Bool) (e : PE) :
    step empty occupied old (.Err e) = (.Err e,old) := rfl

theorem decoded_post (empty old value : Node) (occupied : Bool) :
    (step empty occupied old (.Ok value)).2 = value := by
  dsimp only [step]
  split <;> rfl

/-- A rejecting empty-root check has ALREADY overwritten the selected node. -/
theorem reject_after_write (empty old value : Node) (different : value ≠ empty) :
    step empty false old (.Ok value) = (.Err .InvalidAccountData,value) := by
  simp [step,different]

/-- Library-level frame construction. Applying it to the actual iter_mut
borrow is a separate missing caller association, never address-implies-payload. -/
def write (frontier : Fin 20 → Node) (position : Fin 20) (value : Node) : Fin 20 → Node :=
  fun other => if other = position then value else frontier other

theorem written (frontier : Fin 20 → Node) (position : Fin 20) (value : Node) :
    write frontier position value position = value := by simp only [write,ite_true]

theorem frame (frontier : Fin 20 → Node) (position other : Fin 20) (value : Node)
    (different : other ≠ position) : write frontier position value other = frontier other := by
  simp only [write,if_neg different]

/-- Different element updates preserve the earlier selected cell. -/
theorem disjoint_chain (frontier : Fin 20 → Node) (a b : Fin 20)
    (x y : Node) (different : a ≠ b) :
    write (write frontier a x) b y a = x := by
  rw [frame _ b a y different,written]

#print axioms decode_error
#print axioms decoded_post
#print axioms reject_after_write
#print axioms written
#print axioms frame
#print axioms disjoint_chain
end NJD_LaneStep
end
