import R1Z.PV_RunJoin_WeightCarrier46
import R1Z.PV_RunJoin_CoefficientRow44
import R1Z.PV_RunJoin_CoefficientRowMath44
import R1Z.ProverCommitInactiveRow49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightRow46
open Aeneas Aeneas.Std Result

theorem permutation (j : Usize) :
    PV_B2_D_RowSource.suffix0 j 0#usize=PV_CB3_WeightsMachineRow.row j := by
  have hz : Usize.wrapping_shl (Usize.wrapping_shr j 6#u32 &&& 3#usize) 0#u32 =
      Usize.wrapping_shr j 6#u32 &&& 3#usize :=
    PV_RunJoin_CoefficientRow44.shift_zero _
      (PV_CB3_WeightsMachineRow.digit_bound j 6#u32 (by decide))
  apply UScalar.eq_of_val_eq
  simp only [PV_B2_D_RowSource.suffix0,PV_B2_D_RowSource.suffix1,
    PV_B2_D_RowSource.suffix2,PV_B2_D_RowSource.suffix3,
    PV_B2_D_RowSource.suffix4,PV_B2_D_RowSource.suffix5,
    PV_B2_D_RowSource.digit0,PV_B2_D_RowSource.digit1,
    PV_B2_D_RowSource.digit2,PV_B2_D_RowSource.digit3,
    PV_B2_D_RowSource.digit4,PV_CB3_WeightsMachineRow.row,
    PV_CB3_WeightsMachineRow.digit,hz,PV_CB3_WeightsMachineRow.or_value]
  simp only [show (0#usize).val=0 from rfl,Nat.zero_or]

theorem row (j : Usize) :
    PV_B2_251c1.host_weights.host_row .S2 j=AspisR1InactiveOwner49.owned.row j := by
  obtain ⟨r,hr,hv⟩ := ProverCommitInactiveRow49.row_exact j
  rw [PV_B2_D_RowSource.S2,permutation,hr]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_CoefficientRowMath44.value,hv]
#print axioms permutation
#print axioms row
end R1Z.PV_RunJoin_WeightRow46
