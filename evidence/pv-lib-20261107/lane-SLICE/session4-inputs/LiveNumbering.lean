import PV_STX2_StoreCounter
set_option autoImplicit false
namespace PV_STX2_LiveNumbering
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine
/-- Conditional on owner acceptance of the translator patch. A saved native
child is allocated strictly above its caller and below the unused counter. -/
def WaitingBound (a counter : Nat) (waiting : Option (PV_STX2_Native.Waiting Data)) : Prop :=
  match waiting with
  | some q => match q.request with
    | .child _ b _ => a < b ∧ b < counter
    | _ => True
  | none => True
/-- Conditional on owner acceptance of the translator patch. Saved frames
are strictly older, and every pending child has already been allocated. -/
def StackBelow (counter ceiling : Nat) : List Frame → Prop
  | [] => True
  | f :: fs => f.activation < ceiling ∧ WaitingBound f.activation counter f.waiting ∧
      StackBelow counter f.activation fs
/-- Conditional on owner acceptance of the translator patch. Interpreter
invariant, independent of cells and OWNER registration. -/
def Numbered (c : Config) : Prop :=
  c.frame.activation < c.store.nextActivation ∧
  WaitingBound c.frame.activation c.store.nextActivation c.frame.waiting ∧
  StackBelow c.store.nextActivation c.frame.activation c.callers
/-- Conditional on owner acceptance of the translator patch. Increasing the
unused counter cannot invalidate any saved child number. -/
theorem waiting_mono {a k l : Nat} {q : Option (PV_STX2_Native.Waiting Data)}
    (h : WaitingBound a k q) (le : k ≤ l) : WaitingBound a l q := by
  cases q with
  | none => trivial
  | some q =>
    cases hr : q.request <;> simp only [WaitingBound,hr] at h ⊢
    exact ⟨h.1,Nat.lt_of_lt_of_le h.2 le⟩
/-- Conditional on owner acceptance of the translator patch. Stack numbering
is monotone in the unused activation counter. -/
theorem stack_mono {k l ceiling : Nat} {fs : List Frame}
    (h : StackBelow k ceiling fs) (le : k ≤ l) : StackBelow l ceiling fs := by
  induction fs generalizing ceiling with
  | nil => trivial
  | cons f fs ih => exact ⟨h.1,waiting_mono h.2.1 le,ih h.2.2⟩
/-- Conditional on owner acceptance of the translator patch. Every saved
caller is strictly older than the active frame, including unregistered cells. -/
theorem caller_older {k ceiling : Nat} {fs : List Frame} (h : StackBelow k ceiling fs)
    (f : Frame) (mem : f ∈ fs) : f.activation < ceiling := by
  induction fs generalizing ceiling with
  | nil => cases mem
  | cons g fs ih =>
    rcases List.mem_cons.mp mem with e | mem
    · subst f; exact h.1
    · exact Nat.lt_trans (ih h.2.2 mem) h.1
/-- Conditional on owner acceptance of the translator patch. Actual program
entry establishes the invariant, for every store and capture list. -/
theorem initial (p : PV_STX2_SliceSyntax.Program) (captures : List Data) (s : Store Data) :
    Numbered (enter p captures s) := by
  simp only [Numbered,enter,PV_STX2_StoreCounter.arguments,WaitingBound,StackBelow]
  exact ⟨Nat.lt_succ_self _,trivial,trivial⟩
/-- Conditional on owner acceptance of the translator patch. Pushing an
already issued structured child preserves the entire stack invariant. -/
theorem push (c : Config) (program : PV_STX2_SliceSyntax.Program)
    (callee : Data) (b : Nat) (vs : List Data) (q : PV_STX2_Native.Waiting Data)
    (numbered : Numbered c) (waiting : c.frame.waiting = some q)
    (request : q.request = .child callee b vs) :
    Numbered {c with frame := {activation := b,remaining := program.body},callers := c.frame :: c.callers} := by
  have h := numbered.2.1
  simp only [WaitingBound,waiting,request] at h
  exact ⟨h.2,trivial,h.1,numbered.2.1,numbered.2.2⟩
#print axioms WaitingBound
#print axioms StackBelow
#print axioms Numbered
#print axioms waiting_mono
#print axioms stack_mono
#print axioms caller_older
#print axioms initial
#print axioms push
end PV_STX2_LiveNumbering
