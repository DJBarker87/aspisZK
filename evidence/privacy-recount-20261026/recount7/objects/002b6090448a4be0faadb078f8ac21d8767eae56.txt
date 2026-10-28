import R1Z.PV_B2_C_RawWeights253Funs
import R1Z.PV_B2_C_TableRange
set_option autoImplicit false
namespace PV_B2_C_DRowRange
open Aeneas Aeneas.Std Result PV_B2_253c1

/-- Every valid D table index returns a row below 1024; invalid indices retain
arrayOutOfBounds by ErrorRepair. No original/copy table association is assumed here. -/
theorem source (j : Usize) (hj : j.val < (1024#usize).val) :
    ∃ r : Usize, host_weights.host_row .D j = ok r ∧ r.val < 1024 := by
  obtain ⟨x,hx,hr⟩ := PV_B2_C_TableRange.read_range j hj
  refine ⟨UScalar.cast .Usize x,?_,?_⟩
  · simp only [host_weights.host_row,host_weights.HOST_COEFFICIENT_TO_ROW,hx,bind_tc_ok]
  · simp only [UScalar.cast,UScalar.val,BitVec.zeroExtend_eq_setWidth,BitVec.toNat_setWidth]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hr

#print axioms source
end PV_B2_C_DRowRange
