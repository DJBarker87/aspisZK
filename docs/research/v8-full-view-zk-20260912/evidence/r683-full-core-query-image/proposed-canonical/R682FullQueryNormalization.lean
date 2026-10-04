import AspisV8R19.R679GeneralResidualMoments
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R682FullQueryNormalization
open AspisR19 AspisV8R17 AspisCircleTensorBinding
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]
def extendLow256 (r : Fin 22 → F) (i : Fin 256) : F :=
  if h : i.val < 22 then r ⟨i.val,h⟩ else 0

theorem extendLow256_sum (r : Fin 22 → F) (w : Fin 256 → F) :
    ∑ i, extendLow256 r i*w i = ∑ j : Fin 22, r j*w ⟨j.val,by omega⟩ := by
  rw [Fin.sum_univ_add (a:=22) (b:=234)]
  simp [extendLow256, Fin.castAdd, Fin.natAdd, Fin.castLE]

def evaluate256 (v : Fin 256 → F) (x : F) : F :=
  ∑ d, v d*naturalLineValue x d.val
theorem full_query_normalization (q : HighRepairInvariant.Index 256 → F)
    (alpha : F) (t : Fin 22 → F) (ht : Function.Injective t)
    (hf : ∀ d, R370KernelEvaluation.firstFold 256 alpha q d = 0) :
    ∃ v : HighRepairInvariant.Index 256 → F,
      (∀ slot : Fin 4, ∀ root : Fin 22,
        evaluate256 (fun d => v (d,slot)) (t root) = 0) ∧
      (∀ d, R370KernelEvaluation.firstFold 256 alpha v d = 0) ∧
      (∀ i : HighRepairInvariant.Index 256, 22 ≤ i.1.val → v i = q i) := by
  let low : Fin 4 → Fin 22 → F := fun s => Classical.choose
    (AspisV8R16.natural_eval_surjective t ht
      (fun root => evaluate256 (fun d => q (d,s)) (t root)))
  have hl (s : Fin 4) (root : Fin 22) :
      evaluate256 (extendLow256 (low s)) (t root) =
        evaluate256 (fun d => q (d,s)) (t root) := by
    have h := congrFun (Classical.choose_spec
      (AspisV8R16.natural_eval_surjective t ht
        (fun root => evaluate256 (fun d => q (d,s)) (t root)))) root
    rw [evaluate256,extendLow256_sum]
    simpa only [Matrix.mulVec,dotProduct,naturalEvalMatrix,naturalLineValue_eq_eval,mul_comm] using h
  let corr : HighRepairInvariant.Index 256 → F := fun i =>
    if i.2 = 0 then -alpha*extendLow256 (low 1) i.1 -
      alpha^2*extendLow256 (low 2) i.1-alpha^3*extendLow256 (low 3) i.1
    else extendLow256 (low i.2) i.1
  have hq0 (d : Fin 256) : q (d,0) =
      -alpha*q (d,1)-alpha^2*q (d,2)-alpha^3*q (d,3) := by
    have h := hf d
    simp only [R370KernelEvaluation.firstFold,Fin.sum_univ_succ,
      Fin.val_zero,Fin.val_succ,pow_zero,mul_one] at h
    simp at h
    linear_combination h
  have heq0 (y : F) : evaluate256 (fun d => q (d,0)) y =
      -alpha*evaluate256 (fun d => q (d,1)) y -
      alpha^2*evaluate256 (fun d => q (d,2)) y -
      alpha^3*evaluate256 (fun d => q (d,3)) y := by
    simp only [evaluate256,hq0,sub_mul,mul_assoc,Finset.sum_sub_distrib,Finset.mul_sum]
  have hc (root : Fin 22) (slot : Fin 4) :
      evaluate256 (fun d => corr (d,slot)) (t root) =
        evaluate256 (fun d => q (d,slot)) (t root) := by
    by_cases hs : slot = 0
    · subst slot
      simp only [corr,if_pos rfl,evaluate256,sub_mul,mul_assoc,
        Finset.sum_sub_distrib,Finset.mul_sum]
      rw [← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum]
      change -alpha*evaluate256 (extendLow256 (low 1)) (t root) -
        alpha^2*evaluate256 (extendLow256 (low 2)) (t root) -
        alpha^3*evaluate256 (extendLow256 (low 3)) (t root) = _
      rw [hl,hl,hl]
      exact (heq0 (t root)).symm
    · simp only [corr,if_neg hs]
      exact hl slot root
  have hcf (d : Fin 256) : R370KernelEvaluation.firstFold 256 alpha corr d = 0 := by
    simp only [R370KernelEvaluation.firstFold,Fin.sum_univ_succ,corr,
      Fin.val_zero,Fin.val_succ]
    norm_num only
    simp
    ring
  refine ⟨fun i => q i-corr i,?_,?_,?_⟩
  · intro slot root
    simp only [evaluate256,sub_mul,Finset.sum_sub_distrib]
    change evaluate256 (fun d => q (d,slot)) (t root) -
      evaluate256 (fun d => corr (d,slot)) (t root) = 0
    rw [hc,sub_self]
  · intro d
    simp only [R370KernelEvaluation.firstFold,sub_mul,Finset.sum_sub_distrib]
    change R370KernelEvaluation.firstFold 256 alpha q d -
      R370KernelEvaluation.firstFold 256 alpha corr d = 0
    rw [hf,hcf,sub_self]
  · intro i hi
    have hz (s : Fin 4) : extendLow256 (low s) i.1 = 0 := by
      simp only [extendLow256,dif_neg (by omega : ¬i.1.val<22)]
    simp only [corr,hz,mul_zero,neg_mul,neg_zero,sub_zero,ite_self]
#print axioms extendLow256_sum
#print axioms full_query_normalization
end
end AspisV8R19.R682FullQueryNormalization
