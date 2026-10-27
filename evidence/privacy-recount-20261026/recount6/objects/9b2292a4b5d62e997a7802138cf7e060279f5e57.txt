import R1Z.BuilderForestStdPort

/-! State-preserving adapters for the pinned borrow-back and env-J callback
representations. In particular the returned state is the result of applying
the borrow-back function, not the original callback environment. -/
set_option autoImplicit false
namespace R1Z.BuilderForestCallbackAdapter
open Aeneas Aeneas.Std Result

def borrowToPair {S A : Type}
    (call : S → A → Result (S × (S → S))) (state : S) (arg : A) :
    Result (Unit × S) := do
  let (next, back) ← call state arg
  ok ((), back next)

def stateToPair {S A : Type} (call : S → A → Result S)
    (state : S) (arg : A) : Result (Unit × S) := do
  let next ← call state arg
  ok ((), next)

def pairToState {S A : Type} (call : S → A → Result (Unit × S))
    (state : S) (arg : A) : Result S := do
  let (_, next) ← call state arg
  ok next

theorem state_roundtrip {S A : Type} (call : S → A → Result S)
    (state : S) (arg : A) :
    pairToState (stateToPair call) state arg = call state arg := by
  cases h : call state arg <;> simp [pairToState, stateToPair, h]

theorem pair_roundtrip {S A : Type} (call : S → A → Result (Unit × S))
    (state : S) (arg : A) :
    stateToPair (pairToState call) state arg = call state arg := by
  cases h : call state arg with
  | ok p => rcases p with ⟨u, next⟩; cases u; simp [stateToPair, pairToState, h]
  | fail e => simp [stateToPair, pairToState, h]
  | div => simp [stateToPair, pairToState, h]

theorem borrow_success {S A : Type}
    (call : S → A → Result (S × (S → S))) (state next : S) (arg : A)
    (back : S → S) (h : call state arg = ok (next, back)) :
    borrowToPair call state arg = ok ((), back next) := by
  simp [borrowToPair, h]

/-- The indexed generated closure restores its captured permutation index
while threading the updated callback, even if a returned environment carries
a different index. -/
theorem indexed_borrow {S I : Type} (next : S) (captured returned : I) :
    (fun c : S × I => (c.1, captured)) (next, returned) = (next, captured) := rfl

/-- Tuple adaptation changes only argument packaging, with no oracle call
duplication and no choice of a callback result. -/
theorem uncurry_call {A B C : Type} (call : A → B → Result C) (a : A) (b : B) :
    (fun p : A × B => call p.1 p.2) (a, b) = call a b := rfl

#print axioms state_roundtrip
#print axioms pair_roundtrip
#print axioms borrow_success
#print axioms indexed_borrow
#print axioms uncurry_call
end R1Z.BuilderForestCallbackAdapter
