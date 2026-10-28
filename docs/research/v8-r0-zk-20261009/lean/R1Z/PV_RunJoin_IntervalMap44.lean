import R1Z.ProverCommitArray49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_IntervalMap44
variable {A : Type}

def map (f : A → A) (xs : Nat → A) (start n k : Nat) : A :=
  if start ≤ k ∧ k < start+n then f (xs k) else xs k

theorem zero (f : A → A) (xs : Nat → A) (start : Nat) : map f xs start 0 = xs := by
  funext k
  simp only [map,Nat.add_zero,show ¬(start ≤ k ∧ k < start) from (by omega),if_false]

theorem step (f : A → A) (xs : Nat → A) (start n : Nat) :
    map f (Function.update xs start (f (xs start))) (start+1) n = map f xs start (n+1) := by
  funext k
  by_cases h : k = start
  · subst k
    simp only [map,Function.update_self]
    rw [if_neg (by omega),if_pos (by omega)]
  · simp only [map,Function.update_of_ne h]
    have bounds : (start+1 ≤ k ∧ k < start+1+n) ↔ (start ≤ k ∧ k < start+(n+1)) := by omega
    rw [bounds]

theorem canonical (f : A → A) (P : A → Prop) (xs : Nat → A) (start n size : Nat)
    (hx : ∀ k, k < size → P (xs k)) (hf : ∀ x, P (f x)) :
    ∀ k, k < size → P (map f xs start n k) := by
  intro k hk
  unfold map
  split
  · exact hf _
  · exact hx k hk
#print axioms zero
#print axioms step
#print axioms canonical
end R1Z.PV_RunJoin_IntervalMap44
