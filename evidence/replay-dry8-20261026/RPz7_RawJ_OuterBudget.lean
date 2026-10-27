import RPz7_GExq_OuterLower
import RPz7_GExp_CountLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_OuterBudget
open Aeneas Aeneas.Std Result S2W_Trace
open GExq_OuterLower

def cost {A : Type} : Call A → Nat
  | .op10 _ _ _ _ _ _ _ => 1018
  | .op11 _ _ _ _ _ _ => 903
  | _ => 0

def bounded {A : Type} : Nat → Code A → Prop
  | _, .done _ => True
  | n, .step r k => match r with
    | .ok a => bounded n (k a)
    | _ => True
  | n, .call op k => cost op ≤ n ∧ ∀ a, bounded (n-cost op) (k a)

theorem mono {A : Type} (p : Code A) {m n : Nat} (h : bounded m p) (le : m ≤ n) : bounded n p := by
  induction p generalizing m n with
  | done a => trivial
  | step r k ih => cases r with
    | ok a => exact ih a h le
    | fail e => trivial
    | div => trivial
  | call op k ih =>
    exact ⟨h.1.trans le,fun a => ih a (h.2 a) (Nat.sub_le_sub_right le _)⟩

theorem bind_bound {A B : Type} (p : Code A) (k : A → Code B) (m n : Nat)
    (hp : bounded m p) (hk : ∀ a, bounded n (k a)) : bounded (m+n) (p >>= k) := by
  induction p generalizing m with
  | done a => exact mono _ (hk a) (Nat.le_add_left n m)
  | step r c ih => cases r with
    | ok a => exact ih a m hp
    | fail e => trivial
    | div => trivial
  | call op c ih =>
    refine ⟨hp.1.trans (Nat.le_add_right m n),?_⟩
    intro a
    have h := ih a (m-cost op) (hp.2 a)
    have enough : cost op ≤ m := hp.1
    have same : m-cost op+n = m+n-cost op := by omega
    rw [same] at h
    exact h

theorem then_bound {A B : Type} (p : Code A) (k : A → Code B) (total spent : Nat)
    (le : spent ≤ total) (hp : bounded spent p)
    (hk : ∀ a, bounded (total-spent) (k a)) : bounded total (p >>= k) := by
  have h := bind_bound p k spent (total-spent) hp hk
  have same : spent+(total-spent)=total := by omega
  simpa only [same] using h

theorem pure_bound {A : Type} (n : Nat) (a : A) : bounded n (pure a : Code A) := trivial

theorem lift_bound {A : Type} (n : Nat) (r : Result A) : bounded n (monadLift r : Code A) := by
  cases r <;> trivial

theorem lift_bind {A B : Type} (n : Nat) (r : Result A) (k : A → Code B)
    (hk : ∀ a, bounded n (k a)) : bounded n ((monadLift r : Code A) >>= k) := by
  cases r with
  | ok a => exact hk a
  | fail e => trivial
  | div => trivial

theorem call_bind {A B : Type} (n : Nat) (op : Call A) (k : A → Code B)
    (le : cost op ≤ n) (hk : ∀ a, bounded (n-cost op) (k a)) :
    bounded n (perform op >>= k) := ⟨le,hk⟩

theorem lower_count {A : Type} (impl : {B : Type} → Call B → Oracle B)
    (law : ∀ {B : Type} (op : Call B), GExp_CountLaws.count (cost op) (impl op))
    (p : Code A) (n : Nat) (h : bounded n p) : GExp_CountLaws.count n (lower impl p) := by
  induction p generalizing n with
  | done a => exact GExp_CountLaws.pure_count _ _
  | step r k ih => cases r with
    | ok a => exact ih a n h
    | fail e => exact GExp_CountLaws.lift_count _ (.fail e)
    | div => exact GExp_CountLaws.lift_count _ .div
  | call op k ih =>
    exact GExp_CountLaws.then_count h.1 (law op) (fun a => ih a (n-cost op) (h.2 a))

#print axioms mono
#print axioms bind_bound
#print axioms then_bound
#print axioms pure_bound
#print axioms lift_bound
#print axioms lift_bind
#print axioms call_bind
#print axioms lower_count
end AspisR1.RawJ_OuterBudget
end
