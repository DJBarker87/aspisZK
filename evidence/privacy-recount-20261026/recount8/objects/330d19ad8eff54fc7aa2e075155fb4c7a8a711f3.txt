import R1Z.PV_CB3_WeightsMachineRow
import R1Z.PV_CB3_WeightsPermutation
import D18Transport
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CoefficientRowMath44
open Aeneas Aeneas.Std

theorem value (j : Usize) : (PV_CB3_WeightsMachineRow.row j).val = AspisR1.rowNat j.val := by
  rw [PV_CB3_WeightsMachineRow.row_value,PV_CB3_WeightsPermutation.row_value]
  unfold PV_CB3_WeightsDomain.row PV_CB3_WeightsDomain.digit AspisR1.rowNat
  norm_num only [Nat.reducePow]
  omega

theorem bound (j : Usize) : (PV_CB3_WeightsMachineRow.row j).val < 1024 :=
  PV_CB3_WeightsMachineRow.row_bound j
#print axioms value
#print axioms bound
end R1Z.PV_RunJoin_CoefficientRowMath44
