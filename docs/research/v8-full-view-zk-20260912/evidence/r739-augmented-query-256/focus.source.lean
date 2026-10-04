import AspisV8R19.AugmentedQuerySection
import AspisV8R19.R682FullQueryNormalization

/-! The existing 23-root augmented query normalization, extended from 32
coefficients to the full selected 256 coefficient rows.  This is only finite
field algebra; it does not assert a callback, source execution, or coverage. -/
set_option autoImplicit false
namespace AspisV8R19.R739AugmentedQuery256
open AspisR19 AspisV8R16 AspisCircleTensorBinding
open AspisR19.AugmentedQuerySection
open AspisV8R19.R682FullQueryNormalization
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [NeZero (2 : F)]

def low (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) : Fin 23 → F :=
  Classical.choose (natural_eval_surjective (roots t)
    (roots_injective t ht noneOne)
    (fun i => (naturalLinePoly F d.val).eval (roots t i)))

theorem low_evaluates (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) :
    (naturalEvalMatrix F 23 (roots t)).mulVec (low t ht noneOne d) =
      fun i => (naturalLinePoly F d.val).eval (roots t i) :=
  Classical.choose_spec (natural_eval_surjective (roots t)
    (roots_injective t ht noneOne) _)

theorem low_sum_one (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) :
    ∑ i, low t ht noneOne d i = 1 := by
  have h := congrFun (low_evaluates t ht noneOne d) 0
  simpa [Matrix.mulVec,dotProduct,naturalEvalMatrix,roots,
    ← naturalLineValue_eq_eval,natural_one] using h

def extendLow (r : Fin 23 → F) (i : Fin 256) : F :=
  if h : i.val < 23 then r ⟨i.val,h⟩ else 0

theorem extendLow_sum (r : Fin 23 → F) (w : Fin 256 → F) :
    ∑ i, extendLow r i * w i = ∑ j : Fin 23, r j * w ⟨j.val,by omega⟩ := by
  rw [Fin.sum_univ_add (a := 23) (b := 233)]
  simp [extendLow,Fin.castAdd,Fin.natAdd,Fin.castLE]

def normalized (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d i : Fin 256) : F :=
  (if i=d then 1 else 0)-extendLow (low t ht noneOne d) i

theorem normalized_high (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d i : Fin 256) (hi : 23 ≤ i.val) :
    normalized t ht noneOne d i = if i=d then 1 else 0 := by
  simp [normalized,extendLow,show ¬i.val<23 by omega]

theorem normalized_evaluation (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) (x : F) :
    evaluate256 (normalized t ht noneOne d) x = naturalLineValue x d.val-
      ∑ i : Fin 23, low t ht noneOne d i*naturalLineValue x i.val := by
  simp only [evaluate256,normalized,sub_mul,Finset.sum_sub_distrib]
  rw [extendLow_sum]
  simp

theorem normalized_augmented_root (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) (j : Fin 23) :
    evaluate256 (normalized t ht noneOne d) (roots t j) = 0 := by
  have h := congrFun (low_evaluates t ht noneOne d) j
  simp only [Matrix.mulVec,dotProduct,naturalEvalMatrix] at h
  rw [normalized_evaluation]
  simp only [naturalLineValue_eq_eval]
  rw [show (∑ i : Fin 23, low t ht noneOne d i *
      (naturalLinePoly F i.val).eval (roots t j)) =
      (naturalLinePoly F d.val).eval (roots t j) by simpa [mul_comm] using h]
  exact sub_self _

theorem normalized_query_root (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) (j : Fin 22) :
    evaluate256 (normalized t ht noneOne d) (t j) = 0 := by
  simpa [roots] using normalized_augmented_root t ht noneOne d j.succ

theorem normalized_sum_zero (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) :
    ∑ i, normalized t ht noneOne d i = 0 := by
  simpa [roots,evaluate256,natural_one] using normalized_augmented_root t ht noneOne d 0

theorem constant_low_transport (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) (w : Fin 256 → F)
    (hw : ∀ i, i.val < 23 → w i = w 0) :
    (∑ i, normalized t ht noneOne d i*w i) = w d-w 0 := by
  have hs : (∑ i : Fin 23, low t ht noneOne d i*w ⟨i.val,by omega⟩) =
      (∑ i, low t ht noneOne d i)*w 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hw _ i.isLt]
  simp only [normalized,sub_mul,Finset.sum_sub_distrib]
  rw [extendLow_sum,hs,low_sum_one]
  simp

#print axioms low_evaluates
#print axioms low_sum_one
#print axioms extendLow_sum
#print axioms normalized_high
#print axioms normalized_evaluation
#print axioms normalized_augmented_root
#print axioms normalized_query_root
#print axioms normalized_sum_zero
#print axioms constant_low_transport
end
end AspisV8R19.R739AugmentedQuery256
