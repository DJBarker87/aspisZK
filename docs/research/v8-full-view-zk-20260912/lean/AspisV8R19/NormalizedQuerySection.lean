import AspisV8R16.NaturalCoverage
import AspisV8R17.RawFinalKernel
import Mathlib.Algebra.BigOperators.Fin

/-! Normalize high natural-basis units by the unique low interpolation
remainder. No root distribution, source sampler, or hiding hypothesis.
The section is mathematical; source remainder computation is identified
only after its evaluation equations have been justified. -/
namespace AspisR19.NormalizedQuerySection
open AspisCircleTensorBinding Polynomial
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def low (t : Fin 22 → F) (ht : Function.Injective t) (d : Fin 32) : Fin 22 → F :=
  Classical.choose (AspisV8R16.natural_eval_surjective t ht
    (fun i => (naturalLinePoly F d.val).eval (t i)))

theorem low_evaluates (t : Fin 22 → F) (ht : Function.Injective t) (d : Fin 32) :
    (naturalEvalMatrix F 22 t).mulVec (low t ht d) =
      fun i => (naturalLinePoly F d.val).eval (t i) :=
  Classical.choose_spec (AspisV8R16.natural_eval_surjective t ht _)

theorem low_unique (t : Fin 22 → F) (ht : Function.Injective t) (d : Fin 32)
    (r : Fin 22 → F)
    (hr : (naturalEvalMatrix F 22 t).mulVec r =
      fun i => (naturalLinePoly F d.val).eval (t i)) : r = low t ht d := by
  have hinj : Function.Injective (naturalEvalMatrix F 22 t).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (Matrix.mulVec_surjective_iff_isUnit.mp (AspisV8R16.natural_eval_surjective t ht))
  exact hinj (hr.trans (low_evaluates t ht d).symm)

def extendLow (r : Fin 22 → F) (i : Fin 32) : F :=
  if h : i.val < 22 then r ⟨i.val,h⟩ else 0

def normalized (t : Fin 22 → F) (ht : Function.Injective t) (d i : Fin 32) : F :=
  (if i = d then 1 else 0) - extendLow (low t ht d) i

theorem normalized_high (t : Fin 22 → F) (ht : Function.Injective t)
    (d i : Fin 32) (hi : 22 ≤ i.val) :
    normalized t ht d i = if i = d then 1 else 0 := by
  simp [normalized,extendLow,show ¬i.val < 22 by omega]

omit [NeZero (2 : F)] in
theorem extendLow_sum (r : Fin 22 → F) (w : Fin 32 → F) :
    ∑ i, extendLow r i * w i = ∑ j : Fin 22, r j * w ⟨j.val,by omega⟩ := by
  rw [Fin.sum_univ_add (a := 22) (b := 10)]
  simp [extendLow,Fin.castAdd,Fin.natAdd,Fin.castLE]

def evaluate (v : Fin 32 → F) (x : F) : F :=
  ∑ i, v i * naturalLineValue x i.val

theorem normalized_evaluation (t : Fin 22 → F) (ht : Function.Injective t)
    (d : Fin 32) (x : F) :
    evaluate (normalized t ht d) x = naturalLineValue x d.val -
      ∑ i : Fin 22, low t ht d i * naturalLineValue x i.val := by
  simp only [evaluate,normalized,sub_mul,Finset.sum_sub_distrib]
  rw [extendLow_sum]
  simp

theorem normalized_root (t : Fin 22 → F) (ht : Function.Injective t)
    (d : Fin 32) (j : Fin 22) : evaluate (normalized t ht d) (t j) = 0 := by
  have h := congrFun (low_evaluates t ht d) j
  simp only [Matrix.mulVec, dotProduct, naturalEvalMatrix] at h
  rw [normalized_evaluation]
  simp only [naturalLineValue_eq_eval]
  rw [show (∑ i : Fin 22, low t ht d i * (naturalLinePoly F i.val).eval (t j)) =
    (naturalLinePoly F d.val).eval (t j) by simpa [mul_comm] using h]
  exact sub_self _

def represented (v : Fin 32 → F) : Polynomial F :=
  ∑ i, C (v i) * naturalLinePoly F i.val

omit [NeZero (2 : F)] in
theorem represented_eval (v : Fin 32 → F) (x : F) :
    (represented v).eval x = evaluate v x := by
  simp [represented,evaluate,naturalLineValue_eq_eval,Polynomial.eval_finsetSum]

theorem root_product_dvd [DecidableEq F]
    (t : Fin 22 → F) (ht : Function.Injective t) (d : Fin 32) :
    (∏ x ∈ Finset.univ.image t, (X - C x)) ∣ represented (normalized t ht d) := by
  classical
  apply (AspisV8R17.vanishes_iff_fibre_product_dvd _ _).mp
  intro x hx
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
  rw [represented_eval,normalized_root]

#print axioms low_evaluates
#print axioms low_unique
#print axioms normalized_high
#print axioms extendLow_sum
#print axioms normalized_evaluation
#print axioms normalized_root
#print axioms represented_eval
#print axioms root_product_dvd
end
end AspisR19.NormalizedQuerySection
