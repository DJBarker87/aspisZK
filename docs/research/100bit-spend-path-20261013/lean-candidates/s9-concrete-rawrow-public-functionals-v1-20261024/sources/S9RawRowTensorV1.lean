import S9PointRowTwoFoldV1
import S9TensorRowFiveFactorsV1
import S9QFiveProductTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9RawRowTensorV1
open AspisR1S9PointRowDualFoldModelV1 (rawRow)
open AspisR1S9SharedScalarModelValuesV1 (Table)
open AspisR1S9StatementTensorGenericV1 (tensorRow)
open AspisR1S9QFiveProductTransportV1

/-- The concrete five-factor source model is exactly the symbolic Fin5
tensor product on the SAME table. No source/data/model premise is supplied. -/
theorem rawRow_eq_tensorRow (model : Table) (k : Nat) (j : Fin 1024) :
    rawRow model k j=tensorRow (model k) j := by
  let a := model k 0 (j.val%4)
  let b := model k 1 ((j.val/4)%4)
  let c := model k 2 ((j.val/16)%4)
  let d := model k 3 (((j.val/16)/4)%4)
  let e := model k 4 ((j.val/16)/16)
  have hl : (j.val/16)/16<4 := by have := j.isLt;omega
  have hs : rawRow model k j=(a*b)*((c*d)*e) := by
    simp only [rawRow,AspisR1S9PointRowDualFoldModelV1.highProduct,
      AspisR1S9ConstructorTableNativeTensorV1.highProduct,
      AspisR1S9ActualTensorOuterSemanticsV1.highProduct,Nat.mod_eq_of_lt hl] <;> rfl
  have ht := AspisR1S9TensorRowFiveFactorsV1.tensorRow_eq_five_factors (model k) j
  have hp : tensorRow (model k) j=fieldFive a b c d e :=
    ht.trans (generic_five_projected a b c d e)
  exact hs.trans ((q_five_projected a b c d e).trans hp.symm)

#print axioms rawRow_eq_tensorRow
end AspisR1S9RawRowTensorV1
