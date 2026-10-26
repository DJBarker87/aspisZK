import GExq_OuterLower
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_OuterCredit
open Aeneas Aeneas.Std Result S2W_Trace

def charge {A : Type} : Call A → Nat
  | .op10 _ _ _ _ _ _ _ => 1018
  | .op11 _ _ _ _ _ _ => 903
  | _ => 0

def Credit {A : Type} : Code A → Nat → Prop
  | .done _, _ => True
  | .step r k, n => match r with
    | .ok a => Credit (k a) n
    | _ => True
  | .call op k, n => charge op≤n ∧ ∀ a,Credit (k a) (n-charge op)

theorem pure_credit {A : Type} (a : A) (n : Nat) : Credit (pure a : Code A) n := trivial

theorem lift_credit {A : Type} (r : Result A) (n : Nat) : Credit (monadLift r : Code A) n := by
  cases r <;> trivial

theorem weaken {A : Type} (p : Code A) (n m : Nat) (h : Credit p n) (le : n≤m) : Credit p m := by
  induction p generalizing n m with
  | done a => trivial
  | step r c ih => cases r with
    | ok a => exact ih a n m h le
    | fail e => trivial
    | div => trivial
  | call op c ih =>
    exact ⟨h.1.trans le,fun a=>ih a (n-charge op) (m-charge op) (h.2 a) (Nat.sub_le_sub_right le _)⟩

theorem bind_credit {A B : Type} (p : Code A) (k : A → Code B) (np nk : Nat)
    (hp : Credit p np) (hk : ∀ a,Credit (k a) nk) : Credit (p >>= k) (np+nk) := by
  induction p generalizing np with
  | done a => exact weaken (k a) nk (np+nk) (hk a) (by omega)
  | step r c ih => cases r with
    | ok a => exact ih a np hp
    | fail e => trivial
    | div => trivial
  | call op c ih =>
    refine ⟨by have := hp.1;omega,?_⟩
    intro a
    have eq : np+nk-charge op=(np-charge op)+nk := by have := hp.1;omega
    rw [eq]
    exact ih a (np-charge op) (hp.2 a)

theorem lift_bind_credit {A B : Type} (r : Result A) (k : A → Code B) (n : Nat)
    (hk : ∀ a,Credit (k a) n) : Credit ((monadLift r : Code A) >>= k) n := by
  simpa only [Nat.zero_add] using bind_credit (monadLift r) k 0 n (lift_credit r 0) hk

theorem call_bind_credit {A B : Type} (op : Call A) (k : A → Code B) (n : Nat)
    (paid : charge op≤n) (hk : ∀ a,Credit (k a) (n-charge op)) :
    Credit (perform op >>= k) n := ⟨paid,hk⟩

#print axioms pure_credit
#print axioms lift_credit
#print axioms weaken
#print axioms bind_credit
#print axioms lift_bind_credit
#print axioms call_bind_credit
end AspisR1.RPx_OuterCredit
end
