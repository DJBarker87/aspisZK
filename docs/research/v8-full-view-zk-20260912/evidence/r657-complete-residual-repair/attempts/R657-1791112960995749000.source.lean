import AspisV8R19.R656CombinationStructuredMoment
set_option autoImplicit false
namespace AspisV8R19.R657CompleteResidualRepair
open AspisR19 AspisV8R17 HighRepairInvariant
open R645TwoSwapHighDirections
open R649TwoSwapResidualRepair R650ResidualCombinationKernel R651ResidualKernelRepair
open R652ResidualCoefficientCompletion R654ResidualAlphaNonzero
open R655SourceResidualCompletion R656CombinationStructuredMoment
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def repairTarget (desired : Fin 7 → F) (i : Fin 13) : F :=
  if h : 2 ≤ i.val ∧ i.val < 8 then desired ⟨i.val-2,by omega⟩ else 0

/-- Under the explicit query-table and exact determinant conditions, every
first-fold-compatible ordinary target can be reached with all seven
structured coefficients zero and both retained point equations zero. Every
sparse coin, modeled query evaluation, first fold and balance is preserved.
This does not establish legal-witness target compatibility or an oracle law. -/
theorem complete_residual_repair (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half quarter a b c kappa alpha tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (desired : Fin 7 → F)
    (hd : evalSeven desired alpha = 0)
    (hdet : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z
      previous t ht noneOne).det ≠ 0) :
    ∃ x : Fin 13 → F,
      (∀ k : Fin 7, TwoSwapResidualSource.relation half quarter a b c kappa tau z previous
        false (combination t ht noneOne alpha x) k.val = desired k) ∧
      (∀ k : Fin 7, TwoSwapResidualSource.relation half quarter a b c kappa tau z previous
        true (combination t ht noneOne alpha x) k.val = 0) ∧
      (∀ i : Fin 2, sourcePointFunctional (SourceStatementPoints.points z
        ⟨i.val+1,by omega⟩) (actualMask half a b c (combination t ht noneOne alpha x)) = 0) ∧
      (∀ i : Fin 271, actualCoin (actualMask half a b c
        (combination t ht noneOne alpha x)) i = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22, NormalizedQuerySection.evaluate
        (fun d => combination t ht noneOne alpha x (d,slot)) (t root) = 0) ∧
      (∀ d : Fin 32, R370KernelEvaluation.firstFold 32 alpha
        (combination t ht noneOne alpha x) d = 0) ∧
      (∑ r ∈ TwoSwapSourceTable.inactive, actualMask half a b c
        (combination t ht noneOne alpha x) r) = 0 := by
  obtain ⟨x,hx,hcoins,hquery,hfold,hbalance⟩ := residual_kernel_repair t ht noneOne
    half quarter a b c kappa alpha tau z previous (repairTarget desired) hdet
  have ha := residual_matrix_alpha_ne_zero t ht noneOne half quarter a b c kappa alpha tau z previous hdet
  have hp1 : sourcePointFunctional (SourceStatementPoints.points z 1)
      (actualMask half a b c (combination t ht noneOne alpha x)) = 0 := by
    have h := hx 0
    simpa [ResidualModel.selectedRow, TwoSwapResidualSource.observed, repairTarget,
      TwoSwapSourceWeights.mask, actualMask, SourceMaskTransport.code] using h
  have hp2 : sourcePointFunctional (SourceStatementPoints.points z 2)
      (actualMask half a b c (combination t ht noneOne alpha x)) = 0 := by
    have h := hx 1
    simpa [ResidualModel.selectedRow, TwoSwapResidualSource.observed, repairTarget,
      TwoSwapSourceWeights.mask, actualMask, SourceMaskTransport.code] using h
  have hs : ∀ k : Fin 7, k ≠ 4 → k ≠ 6 → TwoSwapResidualSource.relation
      half quarter a b c kappa tau z previous true (combination t ht noneOne alpha x) k.val = 0 := by
    intro k h4 h6
    fin_cases k
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 8
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 9
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 10
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 11
    · exact False.elim (h4 rfl)
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 12
    · exact False.elim (h6 rfl)
  have hstructured := structured_source_completion half quarter a b c kappa tau alpha z previous
    (combination t ht noneOne alpha x) ha hfold
    (combination_low_structured_moment_zero t ht noneOne half alpha a b c kappa tau x z previous hp1 hp2) hs
  have ho : ∀ k : Fin 7, k ≠ 6 → TwoSwapResidualSource.relation
      half quarter a b c kappa tau z previous false (combination t ht noneOne alpha x) k.val = desired k := by
    intro k h6
    fin_cases k
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 2
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 3
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 4
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 5
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 6
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 7
    · exact False.elim (h6 rfl)
  have he : evalSeven (fun k : Fin 7 => TwoSwapResidualSource.relation half quarter a b c kappa tau z previous
      false (combination t ht noneOne alpha x) k.val - desired k) alpha = 0 := by
    unfold evalSeven
    simp only [sub_mul,Finset.sum_sub_distrib]
    change evalSeven (fun k : Fin 7 => TwoSwapResidualSource.relation half quarter a b c kappa tau z previous
      false (combination t ht noneOne alpha x) k.val) alpha - evalSeven desired alpha = 0
    rw [source_relation_eval_zero half quarter a b c kappa tau alpha z previous false _ hfold,hd,sub_self]
  have hall := ordinary_completion _ alpha ha he (fun k hk => sub_eq_zero.mpr (ho k hk))
  refine ⟨x,fun k => sub_eq_zero.mp (hall k),hstructured,?_,hcoins,hquery,hfold,hbalance⟩
  intro i
  fin_cases i
  · exact hp1
  · exact hp2

#print axioms complete_residual_repair
end
end AspisV8R19.R657CompleteResidualRepair
