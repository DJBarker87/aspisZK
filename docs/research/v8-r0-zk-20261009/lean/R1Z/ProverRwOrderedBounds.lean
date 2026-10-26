import R1Z.ProverRwOrderedMonad
set_option autoImplicit false
namespace R1Z.ProverRwOrderedBounds
open Aeneas Aeneas.Std Result
open ProverRwOrderedOracle

theorem bind_bound {A B : Type} (x : Execution A) (f : A → Execution B)
    (n m : Nat) (hx : x.history.length≤n) (hf : ∀ a,(f a).history.length≤m) :
    (x >>= f).history.length≤n+m := by
  rw [ProverRwOrderedMonad.history_bind]
  cases x.result with
  | ok a => simp only [List.length_append]; exact Nat.add_le_add hx (hf a)
  | fail e => exact Nat.le_trans hx (Nat.le_add_right _ _)
  | div => exact Nat.le_trans hx (Nat.le_add_right _ _)

theorem native_bound {A : Type} (r : Result A) : (native r).history.length≤0 := by rfl
theorem query_bound (hash : Request → Result Answer) (q : Request) :
    (query hash q).history.length≤1 := by rfl
theorem pure_bound {A : Type} (a : A) : (ProverRwOrderedOracle.pure a).history.length≤0 := by rfl
#print axioms bind_bound
#print axioms native_bound
#print axioms query_bound
#print axioms pure_bound
end R1Z.ProverRwOrderedBounds
