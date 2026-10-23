import S9ActualSharedGuardTableV1
import S9ConstructorV3CompleteFactorSemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualSharedGuardConstructorV1
open AspisR1S9ActualWeightsNewBoxNewV3
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9FactorTableSemanticsV1
open AspisR1S9ConstructorTableNativeTensorV1
open AspisR1S9ConstructorV3CompleteFactorSemanticsV1
open AspisR1S9ActualSharedGuardTableV1

/-- The shared optimization's common high factors are derived from the same
accepted constructor and the actual native guard. Neither a factor-model
contract nor equality of modeled rows is supplied by the caller. -/
theorem constructor_and_guard_success_common_factors
    (variant : Variant) (alpha : Vector) (z : Circles) (w : Weights)
    (halpha : VectorCanonical alpha) (hz : PointsCanonical z)
    (hnew : weights_new variant alpha z = .ok (.Ok w)) (folds : Usize)
    (hguard : AspisR1S9ProductionPairCutV1.weights.shared_two_point_guard
      (fromCtorWeights w) folds = .ok true) :
    ∃ model : Table, Meaning w.factors model ∧
      AspisR1S9StatementFactorOuterSemanticsV1.RowsPrefix w.points model 3 ∧
      CircleRows z model ∧
      (∀ i, i<4 → model 0 2 i = model 2 2 i) ∧
      (∀ i, i<4 → model 0 3 i = model 2 3 i) ∧
      (∀ i, highProduct (model 2) i =
        model 0 2 (i%4) * model 0 3 ((i/4)%4) * model 2 4 ((i/16)%4)) := by
  obtain ⟨model,hm,hrows,hcircles,_hpoints,_hvariant,_hextra⟩ :=
    constructor_success_complete_factor_semantics variant alpha z w halpha hz hnew
  obtain ⟨h2,h3,hhigh⟩ := guard_true_table_high_products w model hm folds hguard
  exact ⟨model,hm,hrows,hcircles,h2,h3,hhigh⟩

#print axioms constructor_and_guard_success_common_factors
end AspisR1S9ActualSharedGuardConstructorV1
