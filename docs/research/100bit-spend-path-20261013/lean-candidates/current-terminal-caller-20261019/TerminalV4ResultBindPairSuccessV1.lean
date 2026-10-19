import Aeneas

set_option autoImplicit false

namespace AspisR1.TerminalV4ResultBindPairSuccessV1
open Aeneas Aeneas.Std Result

def bindPair {A B C : Type} (r : Result (A × B)) (f : A → B → Result C) : Result C := do
  let (a, b) ← r
  f a b

theorem bindPair_ok_inv {A B C : Type} (r : Result (A × B))
    (f : A → B → Result C) (c : C)
    (h : bindPair r f = .ok c) :
    ∃ a b, r = .ok (a, b) ∧ f a b = .ok c := by
  cases r with
  | ok pair =>
    cases pair with
    | mk a b => exact ⟨a, b, rfl, h⟩
  | fail e => simp [bindPair] at h
  | div => simp [bindPair] at h

#print axioms bindPair_ok_inv
end AspisR1.TerminalV4ResultBindPairSuccessV1
