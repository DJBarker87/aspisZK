import S9ActualSharedGuardSourceV1
import S9ConstructorTableNativeTensorV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualSharedGuardTableV1
open AspisR1S9ActualSharedGuardSourceV1
open AspisR1S9ActualTensorStoredProductV1
open AspisR1S9ConstructorTableNativeTensorV1
abbrev ExactQM := AspisR1.ExtractedCurrentQM31Exact.QM31Exact

private theorem array_read_lookup {A : Type} {n : Usize} (a : Array A n) (i : Usize) (v : A)
    (h : Array.index_usize a i = .ok v) : a.val[i.val]?=some v := by
  unfold Array.index_usize at h
  cases hr : a[i]? with
  | none => simp [hr] at h
  | some original =>
    rw [hr] at h
    have he : original=v := Result.ok.inj h
    exact he ▸ (by simpa using hr)

/-- The source guard's raw equality gives identical decoded factor functions,
including failed coefficient lookups. No canonical input is needed. -/
theorem guard_true_stored_factors (self : weights.Weights) (folds : Usize)
    (h : weights.shared_two_point_guard self folds = .ok true) :
    (∀ i, storedFactor self 0#usize 2 i = storedFactor self 2#usize 2 i) ∧
    (∀ i, storedFactor self 0#usize 3 i = storedFactor self 2#usize 3 i) := by
  obtain ⟨r0,r2,c02,c22,c03,c23,hr0,hr2,h02,h22,h03,h23,e2,e3⟩ :=
    guard_true_raw_cells self folds h
  constructor
  · intro i
    unfold storedFactor
    simp only [array_read_lookup _ _ _ hr0,array_read_lookup _ _ _ hr2,
      array_read_lookup _ _ _ h02,array_read_lookup _ _ _ h22]
    rw [e2]
  · intro i
    unfold storedFactor
    simp only [array_read_lookup _ _ _ hr0,array_read_lookup _ _ _ hr2,
      array_read_lookup _ _ _ h03,array_read_lookup _ _ _ h23]
    rw [e3]

/-- The mathematical high products share dimensions2 and3 because the actual
source guard checked those exact raw receiver cells. Dimension4 remains its
own row-specific factor. This is a constructor-table statement, with table
meaning supplied by the separate same accepted constructor theorem. -/
theorem guard_true_table_high_products
    (w : CW) (model : AspisR1S9FactorTableSemanticsV1.Table)
    (hm : AspisR1S9FactorTableSemanticsV1.Meaning w.factors model)
    (folds : Usize)
    (h : weights.shared_two_point_guard (fromCtorWeights w) folds = .ok true) :
    (∀ i, i<4 → model 0 2 i = model 2 2 i) ∧
    (∀ i, i<4 → model 0 3 i = model 2 3 i) ∧
    (∀ i, highProduct (model 2) i =
      model 0 2 (i%4) * model 0 3 ((i/4)%4) * model 2 4 ((i/16)%4)) := by
  obtain ⟨he2,he3⟩ := guard_true_stored_factors (fromCtorWeights w) folds h
  have h2 : ∀ i, i<4 → model 0 2 i = model 2 2 i := by
    intro i hi
    have h0 := native_stored_factor_model_nat w model hm 0#usize (by decide) 2 i (by decide) hi
    have h2 := native_stored_factor_model_nat w model hm 2#usize (by decide) 2 i (by decide) hi
    exact h0.symm.trans ((he2 i).trans h2)
  have h3 : ∀ i, i<4 → model 0 3 i = model 2 3 i := by
    intro i hi
    have h0 := native_stored_factor_model_nat w model hm 0#usize (by decide) 3 i (by decide) hi
    have h2 := native_stored_factor_model_nat w model hm 2#usize (by decide) 3 i (by decide) hi
    exact h0.symm.trans ((he3 i).trans h2)
  refine ⟨h2,h3,?_⟩
  intro i
  unfold AspisR1S9ActualTensorOuterSemanticsV1.highProduct
  rw [←h2 (i%4) (Nat.mod_lt _ (by decide)),
    ←h3 ((i/4)%4) (Nat.mod_lt _ (by decide))]

#print axioms guard_true_stored_factors
#print axioms guard_true_table_high_products
end AspisR1S9ActualSharedGuardTableV1
