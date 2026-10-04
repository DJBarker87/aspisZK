import AspisV8R19.R679GeneralResidualMoments
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R678ArbitraryPointResidualRepair
open AspisR19 AspisV8R17 HighRepairInvariant
open R645TwoSwapHighDirections
open R649TwoSwapResidualRepair R650ResidualCombinationKernel R651ResidualKernelRepair
open R652ResidualCoefficientCompletion R654ResidualAlphaNonzero
open R655SourceResidualCompletion R656CombinationStructuredMoment
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def repairTarget (desired desiredG : Fin 7 → F) (points : Fin 3 → F) (i : Fin 13) : F :=
  if i.val = 0 then points 1 else if i.val = 1 then points 2 else
  if h : 2 ≤ i.val ∧ i.val < 8 then desired ⟨i.val-2,by omega⟩
  else if h : 8 ≤ i.val then desiredG ⟨if i.val = 12 then 5 else i.val-8,by split_ifs <;> omega⟩ else 0

/-- Every pair of first-fold-compatible coefficient targets is reached by
the exact residual combination, with the structured target boundary retained.
This is a universal conditional image theorem for both relation polynomials;
actual witness target compatibility and transcript probability remain open. -/
theorem arbitrary_point_residual_pair_repair (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half quarter a b c kappa alpha tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (desired desiredG : Fin 7 → F)
    (points : Fin 3 → F) (hquarter : quarter ≠ 0) (hkappa : kappa ≠ 0)
    (hd : evalSeven desired alpha = 0)
    (hdG : evalSeven desiredG alpha = 0)
    (hb : desired 0 + desired 4 = quarter*(kappa*points 0+kappa^2*points 1+kappa^3*points 2))
    (hbG : desiredG 0 + desiredG 4 = quarter*(kappa^2*points 1+kappa^3*points 2))
    (hdet : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z
      previous t ht noneOne).det ≠ 0) :
    ∃ x : Fin 13 → F,
      (∀ k : Fin 7, TwoSwapResidualSource.relation half quarter a b c kappa tau z previous
        false (combination t ht noneOne alpha x) k.val = desired k) ∧
      (∀ k : Fin 7, TwoSwapResidualSource.relation half quarter a b c kappa tau z previous
        true (combination t ht noneOne alpha x) k.val = desiredG k) ∧
      (∀ i : Fin 3, sourcePointFunctional (SourceStatementPoints.points z i)
        (actualMask half a b c (combination t ht noneOne alpha x)) = points i) ∧
      (∀ i : Fin 271, actualCoin (actualMask half a b c
        (combination t ht noneOne alpha x)) i = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22, NormalizedQuerySection.evaluate
        (fun d => combination t ht noneOne alpha x (d,slot)) (t root) = 0) ∧
      (∀ d : Fin 32, R370KernelEvaluation.firstFold 32 alpha
        (combination t ht noneOne alpha x) d = 0) ∧
      (∑ r ∈ TwoSwapSourceTable.inactive, actualMask half a b c
        (combination t ht noneOne alpha x) r) = 0 := by
  obtain ⟨x,hx,hcoins,hquery,hfold,hbalance⟩ := residual_kernel_repair t ht noneOne
    half quarter a b c kappa alpha tau z previous (repairTarget desired desiredG points) hdet
  have ha := residual_matrix_alpha_ne_zero t ht noneOne half quarter a b c kappa alpha tau z previous hdet
  have hp1 : sourcePointFunctional (SourceStatementPoints.points z 1)
      (actualMask half a b c (combination t ht noneOne alpha x)) = points 1 := by
    have h := hx 0
    simpa [ResidualModel.selectedRow, TwoSwapResidualSource.observed, repairTarget,
      R648AugmentedTwoSwapKernel.source_weights_mask_eq] using h
  have hp2 : sourcePointFunctional (SourceStatementPoints.points z 2)
      (actualMask half a b c (combination t ht noneOne alpha x)) = points 2 := by
    have h := hx 1
    simpa [ResidualModel.selectedRow, TwoSwapResidualSource.observed, repairTarget,
      R648AugmentedTwoSwapKernel.source_weights_mask_eq] using h
  have hs : ∀ k : Fin 7, k ≠ 4 → k ≠ 6 → TwoSwapResidualSource.relation
      half quarter a b c kappa tau z previous true (combination t ht noneOne alpha x) k.val = desiredG k := by
    intro k h4 h6
    fin_cases k
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 8
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 9
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 10
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 11
    · exact False.elim (h4 rfl)
    · simpa [ResidualModel.selectedRow,TwoSwapResidualSource.observed,repairTarget] using hx 12
    · exact False.elim (h6 rfl)
  have heG : evalSeven (fun k : Fin 7 => TwoSwapResidualSource.relation half quarter a b c kappa tau z previous
      true (combination t ht noneOne alpha x) k.val - desiredG k) alpha = 0 := by
    unfold evalSeven
    simp only [sub_mul,Finset.sum_sub_distrib]
    change evalSeven (fun k : Fin 7 => TwoSwapResidualSource.relation half quarter a b c kappa tau z previous
      true (combination t ht noneOne alpha x) k.val) alpha - evalSeven desiredG alpha = 0
    rw [source_relation_eval_zero half quarter a b c kappa tau alpha z previous true _ hfold,hdG,sub_self]
  have hbq : TwoSwapResidualSource.relation half quarter a b c kappa tau z previous true
      (combination t ht noneOne alpha x) 0 + TwoSwapResidualSource.relation half quarter a b c kappa tau z previous true
      (combination t ht noneOne alpha x) 4 = quarter*(kappa^2*points 1+kappa^3*points 2) := by
    simp only [TwoSwapResidualSource.relation_eq]
    rw [R653SourceCoefficientBoundary.coefficient_boundary,
      R679GeneralResidualMoments.combination_low_structured_moment_general t ht noneOne half alpha a b c kappa tau x z previous]
    rw [hp1, hp2]
  have hb : (TwoSwapResidualSource.relation half quarter a b c kappa tau z previous true
      (combination t ht noneOne alpha x) (0:Fin 7).val - desiredG 0) +
      (TwoSwapResidualSource.relation half quarter a b c kappa tau z previous true
      (combination t ht noneOne alpha x) (4:Fin 7).val - desiredG 4) = 0 := by
    change (TwoSwapResidualSource.relation half quarter a b c kappa tau z previous true
      (combination t ht noneOne alpha x) 0 - desiredG 0) +
      (TwoSwapResidualSource.relation half quarter a b c kappa tau z previous true
      (combination t ht noneOne alpha x) 4 - desiredG 4) = 0
    linear_combination hbq - hbG
  have hstructured := structured_completion _ alpha ha heG hb
    (fun k h4 h6 => sub_eq_zero.mpr (hs k h4 h6))
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
  have hcoef : TwoSwapResidualSource.relation half quarter a b c kappa tau z previous false
      (combination t ht noneOne alpha x) 0 + TwoSwapResidualSource.relation half quarter a b c kappa tau z previous false
      (combination t ht noneOne alpha x) 4 = quarter *
      (kappa*sourcePointFunctional (SourceStatementPoints.points z 0) (actualMask half a b c (combination t ht noneOne alpha x)) +
      kappa^2*points 1+kappa^3*points 2) := by
    simp only [TwoSwapResidualSource.relation_eq]
    rw [R653SourceCoefficientBoundary.coefficient_boundary,
      R679GeneralResidualMoments.low_plain_moment_general]
    rw [hp1,hp2]
  have h0 := sub_eq_zero.mp (hall (0:Fin 7))
  have h4 := sub_eq_zero.mp (hall (4:Fin 7))
  rw [h0,h4] at hcoef
  have hzero : quarter*(kappa*(sourcePointFunctional (SourceStatementPoints.points z 0)
      (actualMask half a b c (combination t ht noneOne alpha x))-points 0))=0 := by
    linear_combination hb - hcoef
  have hp0 : sourcePointFunctional (SourceStatementPoints.points z 0)
      (actualMask half a b c (combination t ht noneOne alpha x)) = points 0 := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hquarter)).resolve_left hkappa
  refine ⟨x,fun k => sub_eq_zero.mp (hall k),(fun k => sub_eq_zero.mp (hstructured k)),?_,hcoins,hquery,hfold,hbalance⟩
  intro i
  fin_cases i
  · exact hp0
  · exact hp1
  · exact hp2

#print axioms arbitrary_point_residual_pair_repair
end
end AspisV8R19.R678ArbitraryPointResidualRepair
