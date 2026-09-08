import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! Symbolic scaled tensor bridge. No concrete-field enumeration or Rust
translation is claimed. The encoder's twiddle/index bridge is separate. -/
namespace AspisV8.CircleLaurentRecovery
noncomputable section
open Polynomial Finset
variable {K : Type*} [Field K]

def cosinePoly (h : K) (m : ℕ) : K[X] := C h * (X^(2*m)+1)
def sinePoly (g : K) : K[X] := C g * (X^2-1)

theorem cosine_degree (h : K) (m : ℕ) : (cosinePoly h m).natDegree ≤ 2*m := by
  unfold cosinePoly
  apply (natDegree_C_mul_le _ _).trans
  simpa using (natDegree_add_le (X^(2*m) : K[X]) 1)

theorem sine_degree (g : K) : (sinePoly g).natDegree ≤ 2 := by
  unfold sinePoly
  apply (natDegree_C_mul_le _ _).trans
  change (X^(2 : ℕ)-C (1 : K)).natDegree ≤ 2
  rw [natDegree_X_pow_sub_C]

theorem circle_scaled_xy (x y i h g : K) (hi : i^2 = -1)
    (hc : x^2+y^2=1) (hh : 2*h=1) (hg : 2*i*g=1) :
    (cosinePoly h 1).eval (x+i*y) = (x+i*y)*x ∧
    (sinePoly g).eval (x+i*y) = (x+i*y)*y := by
  simp only [cosinePoly, sinePoly, eval_mul, eval_C, eval_add, eval_sub,
    eval_pow, eval_X, eval_one]
  constructor
  · linear_combination -h*hc + h*y^2*hi + (x+i*y)*x*hh
  · linear_combination g*hc - g*y^2*hi + (x+i*y)*y*hg

theorem cosine_double (h z t : K) (hh : 2*h=1) (m : ℕ)
    (ht : (cosinePoly h m).eval z = z^m*t) :
    (cosinePoly h (2*m)).eval z = z^(2*m)*(2*t^2-1) := by
  have hp : (cosinePoly h (2*m)).eval z =
      2*((cosinePoly h m).eval z)^2-z^(2*m) := by
    simp only [cosinePoly, eval_mul, eval_C, eval_add, eval_pow, eval_X, eval_one]
    rw [show 2*(2*m)=(2*m)*2 by omega, pow_mul]
    linear_combination -((z^(2*m)+1)^2*h+z^(2*m))*hh
  rw [hp, ht, mul_pow, show 2*m=m*2 by omega, pow_mul]
  ring

/-- Inactive bit uses X^m, not 1: every tensor row has the same total shift. -/
def selected (m : ℕ) (p : K[X]) (active : Bool) : K[X] :=
  if active then p else X^m

theorem selected_degree (m : ℕ) (p : K[X]) (hp : p.natDegree ≤ 2*m) (a : Bool) :
    (selected m p a).natDegree ≤ 2*m := by
  cases a <;> simp [selected, hp] <;> omega

theorem selected_eval (m : ℕ) (p : K[X]) (z t : K)
    (hp : p.eval z=z^m*t) (a : Bool) :
    (selected m p a).eval z=z^m*(if a then t else 1) := by
  cases a <;> simp [selected, hp]

theorem tensor_degree {ι : Type*} [Fintype ι] (m : ι → ℕ) (p : ι → K[X])
    (hp : ∀ j, (p j).natDegree ≤ 2*m j) (a : ι → Bool) :
    (∏ j, selected (m j) (p j) (a j)).natDegree ≤ 2*∑ j, m j := by
  apply (natDegree_prod_le _ _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => selected_degree _ _ (hp j) _

theorem tensor_eval {ι : Type*} [Fintype ι] (m : ι → ℕ) (p : ι → K[X])
    (z : K) (t : ι → K) (hp : ∀ j, (p j).eval z=z^(m j)*t j) (a : ι → Bool) :
    (∏ j, selected (m j) (p j) (a j)).eval z =
      z^(∑ j, m j) * ∏ j, (if a j then t j else 1) := by
  simp only [eval_prod, selected_eval _ _ _ _ (hp _)]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem message_degree {ι R : Type*} [Fintype ι] [Fintype R]
    (m : ι → ℕ) (p : ι → K[X]) (hp : ∀ j, (p j).natDegree ≤ 2*m j)
    (bits : R → ι → Bool) (coeff : R → K) :
    (∑ r, C (coeff r) * ∏ j, selected (m j) (p j) (bits r j)).natDegree ≤ 2*∑ j,m j := by
  apply natDegree_sum_le_of_forall_le
  intro r _
  exact (natDegree_C_mul_le _ _).trans (tensor_degree m p hp (bits r))

theorem message_eval {ι R : Type*} [Fintype ι] [Fintype R]
    (m : ι → ℕ) (p : ι → K[X]) (z : K) (t : ι → K)
    (hp : ∀ j, (p j).eval z=z^(m j)*t j) (bits : R → ι → Bool) (coeff : R → K) :
    (∑ r, C (coeff r)*∏ j, selected (m j) (p j) (bits r j)).eval z =
      z^(∑ j,m j) * ∑ r, coeff r * ∏ j, (if bits r j then t j else 1) := by
  simp only [eval_finsetSum, eval_mul, eval_C, tensor_eval m p z t hp]
  rw [Finset.mul_sum]
  congr 1
  ext r
  ring

def cosRec (x : K) : ℕ → K
  | 0 => x
  | n+1 => 2*(cosRec x n)^2-1

theorem cosine_rec_eval (x y i h g : K) (hi : i^2 = -1)
    (hc : x^2+y^2=1) (hh : 2*h=1) (hg : 2*i*g=1) (n : ℕ) :
    (cosinePoly h (2^n)).eval (x+i*y) = (x+i*y)^(2^n)*cosRec x n := by
  induction n with
  | zero => simpa [cosRec] using (circle_scaled_xy x y i h g hi hc hh hg).1
  | succ n ih =>
    simpa [cosRec, pow_succ, Nat.mul_comm] using
      cosine_double h (x+i*y) (cosRec x n) hh (2^n) ih

def weight (j : Fin 10) : ℕ := if j.val=0 then 1 else 2^(j.val-1)
def factor (h g : K) (j : Fin 10) : K[X] :=
  if j.val=0 then sinePoly g else cosinePoly h (2^(j.val-1))
def coordinate (x y : K) (j : Fin 10) : K :=
  if j.val=0 then y else cosRec x (j.val-1)

theorem weight_sum : ∑ j : Fin 10, weight j = 512 := by
  norm_num [weight, Fin.sum_univ_succ]

theorem factor_degree (h g : K) (j : Fin 10) :
    (factor h g j).natDegree ≤ 2*weight j := by
  unfold factor weight
  split_ifs
  · simpa using sine_degree g
  · exact cosine_degree _ _

theorem factor_eval (x y i h g : K) (hi : i^2 = -1)
    (hc : x^2+y^2=1) (hh : 2*h=1) (hg : 2*i*g=1) (j : Fin 10) :
    (factor h g j).eval (x+i*y) = (x+i*y)^(weight j)*coordinate x y j := by
  unfold factor weight coordinate
  split_ifs
  · simpa using (circle_scaled_xy x y i h g hi hc hh hg).2
  · exact cosine_rec_eval x y i h g hi hc hh hg _

/-- A single polynomial chosen from the message works at EVERY circle point.
No adaptive pointwise choice of an RS polynomial appears in the conclusion. -/
theorem natural_tensor_embedding (i h g : K) (hi : i^2 = -1)
    (hh : 2*h=1) (hg : 2*i*g=1) (bits : Fin 1024 → Fin 10 → Bool)
    (coeff : Fin 1024 → K) :
    ∃ P : K[X], P.natDegree ≤ 1024 ∧ ∀ x y : K, x^2+y^2=1 →
      P.eval (x+i*y) = (x+i*y)^512 *
        ∑ r, coeff r * ∏ j, (if bits r j then coordinate x y j else 1) := by
  refine ⟨∑ r, C (coeff r)*∏ j, selected (weight j) (factor h g j) (bits r j), ?_, ?_⟩
  · simpa [weight_sum] using message_degree weight (factor h g) (factor_degree h g) bits coeff
  · intro x y hc
    simpa [weight_sum] using message_eval weight (factor h g) (x+i*y)
      (coordinate x y) (factor_eval x y i h g hi hc hh hg) bits coeff

theorem circle_z_nonzero (x y i : K) (hi : i^2 = -1) (hc : x^2+y^2=1) :
    x+i*y ≠ 0 := by
  have h : (x+i*y)*(x-i*y)=1 := by linear_combination hc-y^2*hi
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

/-- The decoder's finite source-image check is global once the tensor and
sample-index bridges hold. The supplied candidate is NOT assumed in the image. -/
theorem checked_image_global {n : ℕ} (hn : 1024<n)
    (i h g : K) (hi : i^2 = -1) (hh : 2*h=1) (hg : 2*i*g=1)
    (bits : Fin 1024 → Fin 10 → Bool) (coeff : Fin 1024 → K)
    (xs ys : Fin n → K) (hc : ∀ s, (xs s)^2+(ys s)^2=1)
    (distinct : Function.Injective (fun s => xs s+i*ys s))
    (P : K[X]) (hP : P.natDegree ≤ 1024)
    (checked : ∀ s, P.eval (xs s+i*ys s) = (xs s+i*ys s)^512 *
      ∑ r, coeff r * ∏ j, (if bits r j then coordinate (xs s) (ys s) j else 1)) :
    ∀ x y : K, x^2+y^2=1 → P.eval (x+i*y) = (x+i*y)^512 *
      ∑ r, coeff r * ∏ j, (if bits r j then coordinate x y j else 1) := by
  obtain ⟨Q,hQ,evalQ⟩ := natural_tensor_embedding i h g hi hh hg bits coeff
  have eq : P=Q := eq_of_natDegree_lt_card_of_eval_eq P Q distinct
    (fun s => (checked s).trans (evalQ (xs s) (ys s) (hc s)).symm)
    (by rw [Fintype.card_fin]; exact (max_le hP hQ).trans_lt hn)
  simpa [eq] using evalQ

/-- Totalization changes no correctly decoded symbol, including zero. -/
theorem totalized_agrees {I : Type*} (raw : I → Option K) (code : I → K)
    (good : Set I) (h : ∀ i ∈ good, raw i=some (code i)) :
    ∀ i ∈ good, (raw i).getD 0=code i := by
  intro i hi
  simp [h i hi]

/-- One common fibre error budget controls every slot and semantic column;
totalizing failed decodes cannot add a bad fibre outside that budget. -/
theorem totalized_bad_fibres_le {F S C : Type*} [DecidableEq K] [Fintype F] [Fintype S] [Fintype C]
    (raw : F → S → C → Option K) (code : F → S → C → K) :
    (Finset.univ.filter fun f => ∃ s c, (raw f s c).getD 0 ≠ code f s c).card ≤
    (Finset.univ.filter fun f => ∃ s c, raw f s c ≠ some (code f s c)).card := by
  classical
  apply Finset.card_le_card
  intro f hf
  obtain ⟨s,c,h⟩ := (Finset.mem_filter.mp hf).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,s,c,?_⟩
  intro heq
  exact h (by simp [heq])

#print axioms circle_scaled_xy
#print axioms cosine_double
#print axioms tensor_degree
#print axioms tensor_eval
#print axioms message_degree
#print axioms message_eval
#print axioms totalized_agrees
#print axioms natural_tensor_embedding
#print axioms circle_z_nonzero
#print axioms checked_image_global
#print axioms totalized_bad_fibres_le
end
end AspisV8.CircleLaurentRecovery
