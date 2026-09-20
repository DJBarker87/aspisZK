import AspisV8R16.FinalConsistency
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

/-! Exact polynomial description of the raw-zero/final-zero kernel.
Quotient image, legal-mask support, source basis conversion and remaining
observations are NOT discharged by this lemma. -/
set_option autoImplicit false
namespace AspisV8R17
open Polynomial
open scoped BigOperators
variable {F : Type*} [Field F]

theorem four_zero_slots (x y a b c d : F)
    (h4 : (4 : F) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (h0 : a+b*y+c*x+d*x*y=0) (h1 : a-b*y+c*x-d*x*y=0)
    (h2 : a-b*y-c*x+d*x*y=0) (h3 : a+b*y-c*x-d*x*y=0) :
    a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  have ha : (4:F)*a=0 := by linear_combination h0+h1+h2+h3
  have hb : ((4:F)*y)*b=0 := by linear_combination h0-h1-h2+h3
  have hc : ((4:F)*x)*c=0 := by linear_combination h0+h1-h2-h3
  have hd : ((4:F)*x*y)*d=0 := by linear_combination h0-h1+h2-h3
  exact ⟨(mul_eq_zero.mp ha).resolve_left h4,
    (mul_eq_zero.mp hb).resolve_left (mul_ne_zero h4 hy),
    (mul_eq_zero.mp hc).resolve_left (mul_ne_zero h4 hx),
    (mul_eq_zero.mp hd).resolve_left (mul_ne_zero (mul_ne_zero h4 hx) hy)⟩

theorem vanishes_iff_fibre_product_dvd (s : Finset F) (p : Polynomial F) :
    (∀ t ∈ s, p.eval t=0) ↔ (∏ t ∈ s, (X-C t)) ∣ p := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => simp
  | @insert t s ht ih =>
    constructor
    · intro h
      have hroot : (X-C t) ∣ p := dvd_iff_isRoot.mpr (h t (Finset.mem_insert_self _ _))
      obtain ⟨q,rfl⟩ := hroot
      have hq : ∀ u ∈ s, q.eval u=0 := by
        intro u hu
        have hu_ne : u ≠ t := by intro he; subst u; exact ht hu
        have hh := h u (Finset.mem_insert_of_mem hu)
        simp only [eval_mul, eval_sub, eval_X, eval_C] at hh
        exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hu_ne)
      obtain ⟨r,hr⟩ := (ih q).mp hq
      refine ⟨r, ?_⟩
      rw [Finset.prod_insert ht, hr, mul_assoc]
    · intro hp u hu
      have hd : (X-C u) ∣ ∏ t ∈ insert t s, (X-C t) := Finset.dvd_prod_of_mem _ hu
      exact dvd_iff_isRoot.mp (dvd_trans hd hp)

theorem zero_fold_raw_kernel (s : Finset F) (x y : F → F)
    (a b c d : Polynomial F) (alpha : F)
    (h4 : (4 : F) ≠ 0) (hx : ∀ t ∈ s, x t ≠ 0) (hy : ∀ t ∈ s, y t ≠ 0)
    (foldZero : a + C alpha*b + C (alpha^2)*c + C (alpha^3)*d = 0) :
    (∀ t ∈ s,
      a.eval t+b.eval t*y t+c.eval t*x t+d.eval t*x t*y t=0 ∧
      a.eval t-b.eval t*y t+c.eval t*x t-d.eval t*x t*y t=0 ∧
      a.eval t-b.eval t*y t-c.eval t*x t+d.eval t*x t*y t=0 ∧
      a.eval t+b.eval t*y t-c.eval t*x t-d.eval t*x t*y t=0) ↔
    (∏ t ∈ s, (X-C t)) ∣ b ∧
    (∏ t ∈ s, (X-C t)) ∣ c ∧
    (∏ t ∈ s, (X-C t)) ∣ d := by
  constructor
  · intro h
    have roots : ∀ t ∈ s, b.eval t=0 ∧ c.eval t=0 ∧ d.eval t=0 := by
      intro t ht
      obtain ⟨h0,h1,h2,h3⟩ := h t ht
      exact (four_zero_slots (x t) (y t) _ _ _ _ h4 (hx t ht) (hy t ht) h0 h1 h2 h3).2
    exact ⟨(vanishes_iff_fibre_product_dvd s b).mp (fun t ht => (roots t ht).1),
      (vanishes_iff_fibre_product_dvd s c).mp (fun t ht => (roots t ht).2.1),
      (vanishes_iff_fibre_product_dvd s d).mp (fun t ht => (roots t ht).2.2)⟩
  · rintro ⟨hb,hc,hd⟩ t ht
    have eb := (vanishes_iff_fibre_product_dvd s b).mpr hb t ht
    have ec := (vanishes_iff_fibre_product_dvd s c).mpr hc t ht
    have ed := (vanishes_iff_fibre_product_dvd s d).mpr hd t ht
    have ea := congrArg (Polynomial.eval t) foldZero
    simp only [eval_add, eval_mul, eval_C, eval_zero, eb, ec, ed, mul_zero, add_zero] at ea
    simp [ea,eb,ec,ed]

#print axioms four_zero_slots
#print axioms vanishes_iff_fibre_product_dvd
#print axioms zero_fold_raw_kernel
end AspisV8R17
