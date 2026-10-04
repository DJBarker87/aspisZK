import AspisV8R19.R657CompleteResidualRepair
set_option autoImplicit false
namespace AspisV8R19.R660FullSourceResidualCorrection
open AspisR19 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open R645TwoSwapHighDirections
open R649TwoSwapResidualRepair R650ResidualCombinationKernel
open R652ResidualCoefficientCompletion R657CompleteResidualRepair
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def fullWeight (half a b c kappa tau : F) (z : Fin 10 → F)
    (previous : Fin 271 → F) (structured : Bool) (i : Index 256) : F :=
  TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous structured
    (4*i.1.val+i.2.val)

def fullRelation (half quarter a b c kappa tau : F) (z : Fin 10 → F)
    (previous : Fin 271 → F) (structured : Bool) (q : Index 256 → F) (k : Nat) : F :=
  coefficient (sourceKernel 256 k quarter) q (fullWeight half a b c kappa tau z previous structured)

def extendCorrection (q : Index 32 → F) (i : Index 256) : F :=
  NormalizedGCore.flatten q (4*i.1.val+i.2.val)

theorem full_extension_relation (half quarter a b c kappa tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (structured : Bool)
    (q : Index 32 → F) (k : Nat) :
    fullRelation half quarter a b c kappa tau z previous structured (extendCorrection q) k =
      TwoSwapResidualSource.relation half quarter a b c kappa tau z previous structured q k := rfl

theorem full_relation_eval_zero (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (structured : Bool)
    (q : Index 256 → F) (hf : ∀ d, R370KernelEvaluation.firstFold 256 alpha q d = 0) :
    evalSeven (fun k : Fin 7 => fullRelation half quarter a b c kappa tau z previous structured q k.val) alpha = 0 :=
  R370KernelEvaluation.kernel_eval_zero_of_first_fold 256 quarter alpha q
    (fullWeight half a b c kappa tau z previous structured) hf

/-- The exact low residual correction cancels the full 1024-coordinate
quadratic source coefficient system around arbitrary full-support R and G
channels. Both first folds, plain R, and structured G conditions are explicit;
no low-support condition is imposed on either incoming channel. The correction
has zero sparse coins, retained points, modeled queries, folds and balance.
Actual witness construction and the adaptive oracle law remain unproved. -/
theorem full_source_residual_correction (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half quarter a b c kappa alpha tau scale : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (r g0 : Index 256 → F)
    (hscale : scale ≠ 0)
    (hf : ∀ d, R370KernelEvaluation.firstFold 256 alpha r d = 0)
    (hfg : ∀ d, R370KernelEvaluation.firstFold 256 alpha g0 d = 0)
    (hr : ∀ k : Fin 7, fullRelation half quarter a b c kappa tau z previous false r k.val = 0)
    (hg : ∀ k : Fin 7, fullRelation half quarter a b c kappa tau z previous true g0 k.val = 0)
    (hdet : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z
      previous t ht noneOne).det ≠ 0) :
    ∃ x : Fin 13 → F,
      (∀ beta : F, ∀ k : Fin 7,
        coefficient (sourceKernel 256 k.val quarter)
          (fun i => (1-beta)*r i + scale*beta*(g0 i + extendCorrection (combination t ht noneOne alpha x) i))
          (fun i => (1-beta)*fullWeight half a b c kappa tau z previous false i +
            beta*fullWeight half a b c kappa tau z previous true i) = 0) ∧
      (∀ i : Fin 2, sourcePointFunctional (SourceStatementPoints.points z
        ⟨i.val+1,by omega⟩) (actualMask half a b c (combination t ht noneOne alpha x)) = 0) ∧
      (∀ i : Fin 271, actualCoin (actualMask half a b c
        (combination t ht noneOne alpha x)) i = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22, NormalizedQuerySection.evaluate
        (fun d => combination t ht noneOne alpha x (d,slot)) (t root) = 0) ∧
      (∀ d : Fin 32, R370KernelEvaluation.firstFold 32 alpha
        (combination t ht noneOne alpha x) d = 0) ∧
      (∑ v ∈ TwoSwapSourceTable.inactive, actualMask half a b c
        (combination t ht noneOne alpha x) v) = 0 := by
  let desired : Fin 7 → F := fun k => (-scale⁻¹) * fullRelation half quarter a b c kappa tau z previous true r k.val -
    fullRelation half quarter a b c kappa tau z previous false g0 k.val
  have hd : evalSeven desired alpha = 0 := by
    have he := full_relation_eval_zero half quarter a b c kappa tau alpha z previous true r hf
    have heg := full_relation_eval_zero half quarter a b c kappa tau alpha z previous false g0 hfg
    calc
      evalSeven desired alpha = (-scale⁻¹) * evalSeven
        (fun k : Fin 7 => fullRelation half quarter a b c kappa tau z previous true r k.val) alpha - evalSeven
        (fun k : Fin 7 => fullRelation half quarter a b c kappa tau z previous false g0 k.val) alpha := by
          simp only [evalSeven, desired, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      _ = 0 := by rw [he,heg,mul_zero,sub_self]
  obtain ⟨x,hordinary,hstructured,hpoints,hcoins,hqueries,hfold,hbalance⟩ :=
    complete_residual_repair t ht noneOne half quarter a b c kappa alpha tau z previous desired hd hdet
  refine ⟨x,?_,hpoints,hcoins,hqueries,hfold,hbalance⟩
  intro beta k
  apply folded_coefficient_zero
  · exact hr k
  · have ho : fullRelation half quarter a b c kappa tau z previous false
        (extendCorrection (combination t ht noneOne alpha x)) k.val = desired k := by
      rw [full_extension_relation]
      exact hordinary k
    have hadd := coefficient_left (sourceKernel 256 k.val quarter) g0
      (extendCorrection (combination t ht noneOne alpha x))
      (fullWeight half a b c kappa tau z previous false) (1:F) (1:F)
    simp only [one_mul] at hadd
    rw [hadd]
    change fullRelation half quarter a b c kappa tau z previous true r k.val +
      scale * (fullRelation half quarter a b c kappa tau z previous false g0 k.val +
        fullRelation half quarter a b c kappa tau z previous false (extendCorrection (combination t ht noneOne alpha x)) k.val) = 0
    rw [ho]
    have cancel (v u : F) : v + scale * (u + ((-scale⁻¹)*v-u)) = 0 := by
      calc
        _ = (1-scale*scale⁻¹)*v := by ring
        _ = 0 := by rw [mul_inv_cancel₀ hscale]; ring
    exact cancel _ _
  · have h1 : fullRelation half quarter a b c kappa tau z previous true
        (extendCorrection (combination t ht noneOne alpha x)) k.val = 0 := by
      rw [full_extension_relation]
      exact hstructured k
    have hadd := coefficient_left (sourceKernel 256 k.val quarter) g0
      (extendCorrection (combination t ht noneOne alpha x))
      (fullWeight half a b c kappa tau z previous true) (1:F) (1:F)
    simp only [one_mul] at hadd
    rw [hadd]
    change fullRelation half quarter a b c kappa tau z previous true g0 k.val +
      fullRelation half quarter a b c kappa tau z previous true (extendCorrection (combination t ht noneOne alpha x)) k.val = 0
    rw [hg k,h1,add_zero]

#print axioms full_extension_relation
#print axioms full_relation_eval_zero
#print axioms full_source_residual_correction
end
end AspisV8R19.R660FullSourceResidualCorrection
