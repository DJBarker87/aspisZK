import NEU_DecoderProjections
set_option autoImplicit false
namespace NEU_EqualityLoop
open Aeneas Aeneas.Std

def equalBytes (left right : List U8) : Bool :=
  match left,right with
  | [],[] => true
  | a::left,b::right => decide (a=b) && equalBytes left right
  | _,_ => false

/-- Symbolic induction; no concrete688-byte recurrence is normalized. -/
theorem prefix_exact (left right : List U8) : equalBytes left right=true ↔ left=right := by
  induction left generalizing right with
  | nil => cases right <;> simp [equalBytes]
  | cons a left ih => cases right <;> simp [equalBytes,ih]

/-- Arbitrary prestate accumulator is retained by one equality window. -/
theorem step_invariant (a b : U8) (same : Bool) :
    (same && decide (a=b))=true ↔ same=true ∧ a=b := by simp

theorem prefix_frame {State : Type} (left right : List U8) (state : State) :
    (equalBytes left right,state,([] : List Unit)) =
    (decide (left=right),state,[]) := by
  have eqv := prefix_exact left right
  have same : equalBytes left right=decide (left=right) := by
    cases h : equalBytes left right <;> simp_all
  rw [same]

#print axioms prefix_exact
#print axioms step_invariant
#print axioms prefix_frame
end NEU_EqualityLoop
