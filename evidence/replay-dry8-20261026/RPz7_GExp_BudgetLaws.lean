import RPz7_GExp_QueryBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_QueryBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

theorem mono {A : Type} (p : Code A) (n m : Nat) (le : n ≤ m)
    (h : bounded n p) : bounded m p := by
  induction p generalizing n m with
  | done a => trivial
  | step r k ih => cases r with
    | ok a => exact ih a n m le h
    | fail e => trivial
    | div => trivial
  | read parts k ih => exact ⟨by have := h.1; omega,fun a => ih a (n-1) (m-1) (by omega) (h.2 a)⟩

theorem bind_bound {A B : Type} (p : Code A) (k : A → Code B) (m n : Nat)
    (hp : bounded m p) (hk : ∀ a, bounded n (k a)) : bounded (m+n) (CheckpointBytes5Effect.bind p k) := by
  induction p generalizing m with
  | done a => exact mono _ n (m+n) (by omega) (hk a)
  | step r next ih => cases r with
    | ok a => exact ih a m hp
    | fail e => trivial
    | div => trivial
  | read parts next ih =>
    have positive := hp.1
    refine ⟨by omega,fun a => ?_⟩
    have rest := ih a (m-1) (hp.2 a)
    have size : m-1+n=m+n-1 := by omega
    simpa only [size] using rest

theorem then_bound {A B : Type} {p : Code A} {k : A → Code B} {total cost : Nat}
    (covered : cost ≤ total) (hp : bounded cost p)
    (hk : ∀ a, bounded (total-cost) (k a)) : bounded total (CheckpointBytes5Effect.bind p k) := by
  have h := bind_bound p k cost (total-cost) hp hk
  have same : cost+(total-cost)=total := by omega
  simpa only [same] using h

theorem pure_bound {A : Type} (n : Nat) (a : A) : bounded n (pure a : Code A) := trivial

theorem lift_bound {A : Type} (n : Nat) (r : Result A) : bounded n (liftResult r) := by
  cases r <;> trivial

theorem lift_bind {A B : Type} (r : Result A) (k : A → Code B) (n : Nat)
    (hk : ∀ a, bounded n (k a)) : bounded n (CheckpointBytes5Effect.bind (liftResult r) k) := by
  cases r with
  | ok a => exact hk a
  | fail e => trivial
  | div => trivial

theorem step_bound {A B : Type} (r : Result A) (k : A → Code B) (n : Nat)
    (hk : ∀ a, bounded n (k a)) : bounded n (.step r k) := by
  cases r with
  | ok a => exact hk a
  | fail e => trivial
  | div => trivial

theorem read_bound (parts : Parts) : bounded 1 (read parts) := ⟨by decide,fun _ => trivial⟩

#print axioms mono
#print axioms bind_bound
#print axioms then_bound
#print axioms pure_bound
#print axioms lift_bound
#print axioms lift_bind
#print axioms step_bound
#print axioms read_bound
end AspisR1.GExp_QueryBudget
end
