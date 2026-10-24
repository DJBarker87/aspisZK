import S9StatementTensorGenericV1
import S9StatementFactorOuterSemanticsV1
import S9SharedSumObservationsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9StatementTensorPublicV1
open AspisR1S9StatementTensorGenericV1
open AspisR1S9StatementCellD18ProgressV1 (pointValue expected)
open AspisR1S9StatementFactorOuterSemanticsV1 (RowsPrefix)
open AspisR1S9FactorTableSemanticsV1 (Table)
open AspisR1S9ConstructorV3StatementCellCanonicalV1 (StatementPoints)
open AspisR1S9SharedSumObservationsV1 (finIndex finIndex_val)
abbrev Q := AspisR1.ExtractedCurrentQM31Exact.QM31Exact

def sourcePoint (points : StatementPoints) (k : Nat) (i : Fin 10) : Q :=
  pointValue points k i.val

/-- Complete SAME source statement-row table semantics supplies each
symbolic D18 factor, using only the already proved source RowsPrefix. -/
theorem statement_row_factors (points : StatementPoints) (model : Table)
    (hrows : RowsPrefix points model 3) (k : Usize) (hk : k.val<3)
    (d : Fin 5) (s : Fin 4) :
    model k.val d.val s.val=pointFactor (sourcePoint points k.val) d s.val := by
  let di := finIndex (by decide : 5≤64) d
  let si := finIndex (by decide : 4≤64) s
  have hd : di.val<5 := by simpa only [di,finIndex_val] using d.isLt
  have hs : si.val<4 := by simpa only [si,finIndex_val] using s.isLt
  have h := hrows k di si hk hd hs hk
  simpa only [di,si,finIndex_val,expected,pointFactor,sourcePoint] using h

/-- Any one of the THREE actual statement rows represents the retained
PUBLIC D18 row functional at every symbolic1024index. No desired table
values or independently chosen public vector is supplied. -/
theorem statement_tensor_row_eq_rowPoint (points : StatementPoints) (model : Table)
    (hrows : RowsPrefix points model 3) (k : Usize) (hk : k.val<3)
    (j : Fin 1024) :
    tensorRow (model k.val) j=AspisR1.rowPoint (sourcePoint points k.val) j :=
  tensorRow_eq_rowPoint (model k.val) (sourcePoint points k.val)
    (statement_row_factors points model hrows k hk) j

#print axioms statement_row_factors
#print axioms statement_tensor_row_eq_rowPoint
end AspisR1S9StatementTensorPublicV1
