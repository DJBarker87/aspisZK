import AspisV8R19.R669ResidualPairRepair
set_option autoImplicit false
namespace AspisV8R19.R670AllPointResidualRepair
open AspisR19 AspisV8R16 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open R645TwoSwapHighDirections R649TwoSwapResidualRepair R669ResidualPairRepair
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- Exact ordinary source moment for a low correction: the two retained point
zeros, balance and image tails leave precisely kappa times point zero. -/
theorem low_plain_moment (half a b c kappa tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (q : Index 32 → F)
    (hp1 : sourcePointFunctional (SourceStatementPoints.points z 1) (actualMask half a b c q) = 0)
    (hp2 : sourcePointFunctional (SourceStatementPoints.points z 2) (actualMask half a b c q) = 0) :
    (∑ d : Fin 32, ∑ s : Fin 4, q (d,s)*TwoSwapResidualModel.weight half a b c kappa z false (d,s)) =
      kappa*sourcePointFunctional (SourceStatementPoints.points z 0) (actualMask half a b c q) := by
  have h := original_weights_transported_pairing half (SourceStatementPoints.points z) kappa
    TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
    (TwoSwapSourceG.original (SourceGConstant.finishCoins half previous))
    (NormalizedGCore.flatten q) a b c tau false
  change rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false)
    (NormalizedGCore.flatten q) =
    (kappa*sourcePointFunctional (SourceStatementPoints.points z 0) (actualMask half a b c q) +
      kappa^2*sourcePointFunctional (SourceStatementPoints.points z 1) (actualMask half a b c q) +
      kappa^3*sourcePointFunctional (SourceStatementPoints.points z 2) (actualMask half a b c q) +
      ∑ i ∈ TwoSwapSourceTable.inactive, actualMask half a b c q i) +
      tau*NormalizedGCore.flatten q 1023 +
      tau^2*(b*NormalizedGCore.flatten q 1022-c*NormalizedGCore.flatten q 1021) at h
  rw [hp1,hp2,actual_mask_balanced,(SourceMaskBoundary.quotient_image_tail q b c).1,
    (SourceMaskBoundary.quotient_image_tail q b c).2] at h
  simp only [mul_zero,add_zero] at h
  unfold TwoSwapResidualSource.quotientWeight at h
  rw [R653SourceCoefficientBoundary.source_pairing_low] at h
  simp only [TwoSwapResidualSource.weight_eq] at h
  simpa only [Fintype.sum_prod_type] using h

/-- The coefficient boundary derives the missing point-zero condition;
quarter and kappa are retained nonzero source conditions. -/
theorem point_zero_of_plain_boundary (half quarter a b c kappa tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (q : Index 32 → F)
    (hquarter : quarter ≠ 0) (hkappa : kappa ≠ 0)
    (hp1 : sourcePointFunctional (SourceStatementPoints.points z 1) (actualMask half a b c q) = 0)
    (hp2 : sourcePointFunctional (SourceStatementPoints.points z 2) (actualMask half a b c q) = 0)
    (hb : TwoSwapResidualSource.relation half quarter a b c kappa tau z previous false q 0 +
      TwoSwapResidualSource.relation half quarter a b c kappa tau z previous false q 4 = 0) :
    sourcePointFunctional (SourceStatementPoints.points z 0) (actualMask half a b c q) = 0 := by
  simp only [TwoSwapResidualSource.relation_eq] at hb
  rw [R653SourceCoefficientBoundary.coefficient_boundary,
    low_plain_moment half a b c kappa tau z previous q hp1 hp2] at hb
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left hquarter)).resolve_left hkappa

/-- Universal conditional residual image for both full seven-coefficient
polynomials, with all three point functionals now preserved. This derives
point zero rather than silently assuming it or dropping it. Legal-witness
compatibility and actual adaptive transcript conditions are still separate. -/
theorem all_point_residual_pair_repair (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half quarter a b c kappa alpha tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (desired desiredG : Fin 7 → F)
    (hquarter : quarter ≠ 0) (hkappa : kappa ≠ 0)
    (hd : R652ResidualCoefficientCompletion.evalSeven desired alpha = 0)
    (hdG : R652ResidualCoefficientCompletion.evalSeven desiredG alpha = 0)
    (hb : desired 0 + desired 4 = 0) (hbG : desiredG 0 + desiredG 4 = 0)
    (hdet : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z previous t ht noneOne).det ≠ 0) :
    ∃ x : Fin 13 → F,
      (∀ k : Fin 7, TwoSwapResidualSource.relation half quarter a b c kappa tau z previous false
        (combination t ht noneOne alpha x) k.val = desired k) ∧
      (∀ k : Fin 7, TwoSwapResidualSource.relation half quarter a b c kappa tau z previous true
        (combination t ht noneOne alpha x) k.val = desiredG k) ∧
      (∀ i : Fin 3, sourcePointFunctional (SourceStatementPoints.points z i)
        (actualMask half a b c (combination t ht noneOne alpha x)) = 0) ∧
      (∀ i : Fin 271, actualCoin (actualMask half a b c (combination t ht noneOne alpha x)) i = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22, NormalizedQuerySection.evaluate
        (fun d => combination t ht noneOne alpha x (d,slot)) (t root) = 0) ∧
      (∀ d : Fin 32, R370KernelEvaluation.firstFold 32 alpha (combination t ht noneOne alpha x) d = 0) ∧
      (∑ i ∈ TwoSwapSourceTable.inactive, actualMask half a b c (combination t ht noneOne alpha x) i) = 0 := by
  obtain ⟨x,hO,hG,hp,hcoins,hquery,hfold,hbalance⟩ :=
    residual_pair_repair t ht noneOne half quarter a b c kappa alpha tau z previous desired desiredG hd hdG hbG hdet
  have hp0 := point_zero_of_plain_boundary half quarter a b c kappa tau z previous
    (combination t ht noneOne alpha x) hquarter hkappa (hp 0) (hp 1) (by
      have h0 := hO 0
      have h4 := hO 4
      simpa using (show TwoSwapResidualSource.relation half quarter a b c kappa tau z previous false
        (combination t ht noneOne alpha x) (0:Fin 7).val +
        TwoSwapResidualSource.relation half quarter a b c kappa tau z previous false
        (combination t ht noneOne alpha x) (4:Fin 7).val = 0 by rw [h0,h4]; exact hb))
  refine ⟨x,hO,hG,?_,hcoins,hquery,hfold,hbalance⟩
  intro i
  fin_cases i
  · exact hp0
  · exact hp 0
  · exact hp 1

#print axioms low_plain_moment
#print axioms point_zero_of_plain_boundary
#print axioms all_point_residual_pair_repair
end
end AspisV8R19.R670AllPointResidualRepair
