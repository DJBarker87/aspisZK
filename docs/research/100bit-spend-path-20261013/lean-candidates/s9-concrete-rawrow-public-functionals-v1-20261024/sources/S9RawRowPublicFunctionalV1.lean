import S9RawRowTensorV1
import S9StatementTensorPublicV1
import S9CircleTensorPublicV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9RawRowPublicFunctionalV1
open AspisR1S9PointRowDualFoldModelV1 (rawRow)
open AspisR1S9SharedScalarModelValuesV1 (Table)
open AspisR1S9RawRowTensorV1

/-- The raw row of the SAME supplied constructor model is the retained D18
functional of its SAME stored source statement-point row. -/
theorem rawRow_statement_point
    (points : AspisR1S9ConstructorV3StatementCellCanonicalV1.StatementPoints)
    (model : Table)
    (hrows : AspisR1S9StatementFactorOuterSemanticsV1.RowsPrefix points model 3)
    (k : Usize) (hk : k.val<3) (j : Fin 1024) :
    rawRow model k.val j=AspisR1.rowPoint
      (AspisR1S9StatementTensorPublicV1.sourcePoint points k.val) j :=
  (rawRow_eq_tensorRow model k.val j).trans
    (AspisR1S9StatementTensorPublicV1.statement_tensor_row_eq_rowPoint points model hrows k hk j)

/-- The other two raw rows use the SAME actual constructor circle input z.
There is no independently chosen point, coordinate pair or public vector. -/
theorem rawRow_circle_weight
    (z : AspisR1S9ConstructorV3CompleteFactorSemanticsV1.Circles) (model : Table)
    (hc : AspisR1S9ConstructorV3CompleteFactorSemanticsV1.CircleRows z model)
    (r : Fin 2) (k : Usize) (hkr : k.val=3+r.val) (j : Fin 1024) :
    rawRow model k.val j=AspisR1.SelectedCircleWeightModel.circleWeight
      (AspisR1S9ConstructorV3QMMulSemanticsV1.decode
        (AspisR1S9CircleTensorPublicV1.sourceCircle z r).x)
      (AspisR1S9ConstructorV3QMMulSemanticsV1.decode
        (AspisR1S9CircleTensorPublicV1.sourceCircle z r).y) j.val :=
  (rawRow_eq_tensorRow model k.val j).trans
    (AspisR1S9CircleTensorPublicV1.circle_tensor_row_eq_circleWeight z model hc r k hkr j)

#print axioms rawRow_statement_point
#print axioms rawRow_circle_weight
end AspisR1S9RawRowPublicFunctionalV1
