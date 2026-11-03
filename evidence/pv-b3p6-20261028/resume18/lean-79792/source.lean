import PV_B3P_ControlFlowAssertion571227
namespace PV_B3P_ResidualSource572227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Untyped local observations preserve enum tags and arbitrary residual payloads.
No pointer, destructor, callback, or formatter semantics are supplied here. -/
inductive Value (α : Type) where
  | payload (value : α)
  | enum (tag : Bool) (value : Value α)
  | scalar (value : Nat)
  | boolean (value : Bool)
  | dead
abbrev Store (α : Type) := Nat → Value α

def put {α : Type} (s : Store α) (slot : Nat) (v : Value α) : Store α :=
  fun queried => if queried = slot then v else s queried

def payload {α : Type} : Value α → Value α
  | .enum true v => v
  | _ => .dead

def discriminant {α : Type} : Value α → Value α
  | .enum false _ => .scalar 0
  | .enum true _ => .scalar 1
  | _ => .dead

def eqOne {α : Type} : Value α → Value α
  | .scalar n => .boolean (n == 1)
  | _ => .dead

inductive Instr where
  | kill (slot : Nat)
  | project (dest src : Nat)
  | breakValue (dest src : Nat)
  | tag (dest src : Nat)
  | equalOne (dest src : Nat)

def step {α : Type} (i : Instr) (s : Store α) : Store α :=
  match i with
  | .kill slot => put s slot .dead
  | .project dest src => put s dest (payload (s src))
  | .breakValue dest src => put s dest (.enum true (s src))
  | .tag dest src => put s dest (discriminant (s src))
  | .equalOne dest src => put s dest (eqOne (s src))

def run {α : Type} : List Instr → Store α → Store α
  | [], s => s
  | i :: rest, s => run rest (step i s)

/-- The complete residual arm from statement 24815 through the state BEFORE
24831. StorageLive and StorageDead both invalidate the observed local. -/
def residualProgram : List Instr :=
  [.kill 17, .project 17 8, .kill 18, .breakValue 18 17,
   .breakValue 7 18, .kill 18, .kill 17, .kill 8,
   .kill 13, .project 13 7, .kill 31, .kill 33,
   .tag 31 13, .equalOne 33 31]

/-- State projection at the assertion, for every prior local store and every
incoming residual value. The matching branch itself supplies the enum tag. -/
def assertionState {α : Type} (prior : Store α) (residual : Value α) : Store α :=
  run residualProgram (put prior 8 (.enum true residual))

theorem assertion_value {α : Type} (prior : Store α) (residual : Value α) :
    assertionState prior residual 33 = .boolean true := by
  simp only [assertionState, residualProgram, run, step, put, payload,
    discriminant, eqOne, Nat.reduceEqDiff, ite_true, ite_false, BEq.rfl]

/-- These are exactly the local states emitted by the captured residual arm;
there is no assumed guard or assumed successful Result in this definition. -/
def Reached {α : Type} (s : Store α) : Prop :=
  ∃ prior residual, s = assertionState prior residual

def condition {α : Type} (s : Store α) : Bool :=
  match s 33 with
  | .boolean b => b
  | _ => false

theorem reached_guard {α : Type} (s : Store α) (reached : Reached s) :
    condition s = true := by
  obtain ⟨prior,residual,rfl⟩ := reached
  rw [condition, assertion_value]

/-- One pattern application consumes the proved source-state guard. -/
theorem source_assertion {α β : Type} (s : Store α) (reached : Reached s)
    (normal first second : Result β) :
    ¬ diagnostic (condition s = true) ∧
      branch (condition s = true) normal first =
        branch (condition s = true) normal second :=
  (assertion (condition s) true normal first second).2 (reached_guard s reached)

#print axioms assertion_value
#print axioms reached_guard
#print axioms source_assertion
end PV_B3P_ResidualSource572227
