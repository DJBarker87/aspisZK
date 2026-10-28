import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace PV_L2B_Guards
-- Mathematical guard laws. Native builder/canonicality/refinement association
-- is retained, never represented by an additional trust item.
def firstFailure : List Bool → Nat
 | [] => 0
 | true :: _ => 1
 | false :: xs => 1+firstFailure xs
theorem passing_trace (n : Nat) : firstFailure (List.replicate n false) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,firstFailure,ih]; omega
#print axioms passing_trace
theorem failed_trace (xs : List Bool) : firstFailure (true::xs) = 1 := rfl
#print axioms failed_trace
theorem zero_guard {A : Type} [Zero A] [DecidableEq A] (x : A) (hx : x=0) : decide (x ≠ 0) = false := by simp [hx]
#print axioms zero_guard
theorem equality_guard {A : Type} [DecidableEq A] (x y : A) (h : x=y) : decide (x ≠ y) = false := by simp [h]
#print axioms equality_guard
theorem active_zero_guard {A : Type} [Zero A] [DecidableEq A] (active : Bool) (x : A) (h : active=true → x=0) : (active && decide (x ≠ 0)) = false := by
  cases active <;> simp_all
#print axioms active_zero_guard
theorem canonical_guard (p x : Nat) (hx : x<p) : decide (p≤x) = false := by simp; omega
#print axioms canonical_guard
theorem modular_canonical (p a b : Nat) (hp : 0<p) : (a+b)%p<p := Nat.mod_lt _ hp
#print axioms modular_canonical
theorem zmod_canonical (p : Nat) [NeZero p] (x : ZMod p) : x.val<p := ZMod.val_lt x
#print axioms zmod_canonical
theorem balanced_dependent {A : Type} [AddGroup A] (sum : A) : sum+(-sum)=0 := add_neg_cancel sum
#print axioms balanced_dependent
theorem balanced_dependent_first {A : Type} [AddGroup A] (sum : A) : (-sum)+sum=0 := neg_add_cancel sum
#print axioms balanced_dependent_first
theorem inactive_balance {I A : Type} [Fintype I] [DecidableEq I] [AddCommGroup A]
    (d : I) (v : I → A) :
    (∑ i : I, if i=d then -(∑ j ∈ Finset.univ.erase d, v j) else v i)=0 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ d)]
  simp only [ite_true]
  have hs : (∑ i ∈ Finset.univ.erase d, if i=d then -(∑ j ∈ Finset.univ.erase d, v j) else v i) = ∑ i ∈ Finset.univ.erase d, v i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [hi.1]
  rw [hs]; exact neg_add_cancel _
#print axioms inactive_balance
theorem padding_total {I A : Type} [Fintype I] [AddCommGroup A]
    (active : I → Bool) (padding : I → A)
    (hz : ∀ i, active i=true → padding i=0)
    (hs : (∑ i : I, if active i then 0 else padding i)=0) :
    (∑ i : I, padding i)=0 := by
  classical
  have h : (∑ i : I, padding i) = ∑ i : I, if active i then 0 else padding i := by
    apply Finset.sum_congr rfl
    intro i hi
    cases ha : active i with
    | false => simp [ha]
    | true => simp [ha,hz i ha]
  exact h.trans hs
#print axioms padding_total
theorem padding_preserves_sum {I A : Type} [Fintype I] [AddCommGroup A]
    (helper padding : I → A) (hh : (∑ i : I, helper i)=0)
    (hp : (∑ i : I, padding i)=0) :
    (∑ i : I, (helper i + padding i))=0 := by rw [Finset.sum_add_distrib,hh,hp,add_zero]
#print axioms padding_preserves_sum
theorem paired_helper_cancels {I A : Type} [Fintype I] [AddCommGroup A] (v : I → A) : (∑ i : I, v i) - (∑ i : I, v i) = 0 := sub_self _
#print axioms paired_helper_cancels
theorem c1_count_guard (count : Nat) (h : count=16) : decide (count ≠ 16)=false := by simp [h]
#print axioms c1_count_guard
theorem mask_count_guard (count : Nat) (h : count=10) : decide (count ≠ 10)=false := by simp [h]
#print axioms mask_count_guard
theorem audit_shortcircuit (a b c d e : Bool) (ha : a=false) (hb : b=false) (hc : c=false) (hd : d=false) (he : e=false) : a || b || c || d || e = false := by simp [ha,hb,hc,hd,he]
#print axioms audit_shortcircuit
theorem helper_option_guard {A : Type} [Zero A] [DecidableEq A] (v : Option A) (h : v=some 0) : decide (v ≠ some 0)=false := by simp [h]
#print axioms helper_option_guard
theorem sumcheck_boundary {A : Type} [AddMonoid A] (v0 v1 running p0 p1 : A)
    (interpolation0 : p0=v0) (interpolation1 : p1=v1)
    (initial : v0+v1=running) : p0+p1=running := by rw [interpolation0,interpolation1,initial]
#print axioms sumcheck_boundary
theorem sumcheck_terminal {A : Type} [DecidableEq A] (oracle running polynomial : A)
    (low_degree_identity : oracle=polynomial) (running_eval : running=polynomial) :
    decide (oracle ≠ running)=false := by simp [low_degree_identity,running_eval]
#print axioms sumcheck_terminal
end PV_L2B_Guards
