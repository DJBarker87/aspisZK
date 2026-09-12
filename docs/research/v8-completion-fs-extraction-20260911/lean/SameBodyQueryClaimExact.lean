import SameBodyQueryClaim
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-! DRAFT pending focused historical compilation.
Exact ring interpretation of the EXISTING source-shaped powers/zip/foldl.
No supplied equality identifies an opaque increment with the desired sum.
Quarter is an explicit public scalar (no inverse-of-four claim needed here).
Machine QM31 kernels and source byte parsing remain independent refinements.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
namespace AspisV8Completion.SameBodyQueryClaimExact
open SameBodyQueryClaim
open scoped BigOperators
variable {R : Type*} [CommRing R]

def ringArithmetic (quarter : R) : Arithmetic R where
  sub := (·-·)
  quarter := fun c => c*quarter
  evaluate7 := fun p alpha => (List.ofFn p).reverse.foldl (fun c a => c*alpha+a) 0
  zero := 0
  add := (·+·)
  mul := (·*·)

theorem powersFrom_exact (quarter rho power : R) (n : Nat) :
    powersFrom (ringArithmetic quarter) rho power n =
      List.ofFn (fun i : Fin n => power*rho^i.val) := by
  induction n generalizing power with
  | zero => simp [powersFrom]
  | succ n ih =>
    change power :: powersFrom (ringArithmetic quarter) rho (power*rho) n = _
    rw [ih, List.ofFn_succ]
    simp only [Fin.val_zero, pow_zero, mul_one]
    apply congrArg (List.cons power)
    apply congrArg List.ofFn
    funext i
    simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]

theorem scales_exact (quarter rho : R) (n : Nat) :
    scales (ringArithmetic quarter) rho n =
      List.ofFn (fun i : Fin n => rho^(i.val+1)) := by
  rw [scales, powersFrom_exact]
  apply congrArg List.ofFn
  funext i
  simp [pow_succ, mul_comm]

theorem zip_ofFn_same {A B : Type*} {n : Nat} (a : Fin n → A) (b : Fin n → B) :
    (List.ofFn a).zip (List.ofFn b) = List.ofFn (fun i => (a i,b i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ, List.zip_cons_cons, ih]

theorem foldl_products (pairs : List (R × R)) (initial : R) :
    pairs.foldl (fun c p => c+p.1*p.2) initial =
      initial+(pairs.map (fun p => p.1*p.2)).sum := by
  induction pairs generalizing initial with
  | nil => simp
  | cons p ps ih => simp [List.foldl_cons,ih,add_assoc]

theorem dot_ofFn_exact (quarter : R) {n : Nat} (a b : Fin n → R) :
    dot (ringArithmetic quarter) (List.ofFn a) (List.ofFn b) =
      ∑ i : Fin n, a i*b i := by
  simp only [dot, ringArithmetic, zip_ofFn_same, foldl_products,zero_add,
    List.map_ofFn,List.sum_ofFn,Function.comp_apply]

theorem increment_exact (quarter rho : R) (opened : Fin 22 → R) :
    increment (ringArithmetic quarter) rho opened =
      ∑ i : Fin 22, rho^(i.val+1)*opened i := by
  rw [increment,scales_exact,dot_ofFn_exact]

theorem injectClaim_exact (quarter prior rho : R) (opened : Fin 22 → R) :
    injectClaim (ringArithmetic quarter) prior rho opened =
      prior+∑ i : Fin 22, rho^(i.val+1)*opened i := by
  change prior+increment (ringArithmetic quarter) rho opened = _
  rw [increment_exact]

/-- Positive source scalar injection minus the injected final-evaluation
scalar equals the degree-q-shaped residual correction. The prior is arbitrary;
no zero-prior or pointwise-success assumption is made. -/
theorem injectClaim_discrepancy (quarter prior rho : R)
    (opened expected : Fin 22 → R) :
    injectClaim (ringArithmetic quarter) prior rho opened -
      (∑ i : Fin 22, rho^(i.val+1)*expected i) =
      prior-rho*∑ i : Fin 22, (expected i-opened i)*rho^i.val := by
  rw [injectClaim_exact]
  have difference :
      (∑ i : Fin 22, rho^(i.val+1)*opened i) -
        (∑ i : Fin 22, rho^(i.val+1)*expected i) =
      -(rho*∑ i : Fin 22, (expected i-opened i)*rho^i.val) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  calc
    _ = prior + ((∑ i : Fin 22, rho^(i.val+1)*opened i) -
        (∑ i : Fin 22, rho^(i.val+1)*expected i)) := by ring
    _ = _ := by rw [difference]; ring

#print injectClaim_discrepancy
#print axioms powersFrom_exact
#print axioms dot_ofFn_exact
#print axioms increment_exact
#print axioms injectClaim_exact
#print axioms injectClaim_discrepancy
end AspisV8Completion.SameBodyQueryClaimExact
