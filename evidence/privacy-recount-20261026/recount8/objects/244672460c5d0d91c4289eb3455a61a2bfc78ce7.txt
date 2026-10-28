import R1Z.PV_RunJoin_CheckedShiftInspect44
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CheckedShift44
open Aeneas Aeneas.Std Result

theorem right (x n : Usize) (hn : n.val < 32) :
    (x >>> n : Result Usize) = .ok (Usize.wrapping_shr x (UScalar.cast .U32 n)) := by
  have width : n.val < UScalarTy.numBits .Usize := lt_of_lt_of_le hn PV_CB3_WeightsMachine.width_min
  change UScalar.shiftRight x n.val = _
  unfold UScalar.shiftRight
  simp only [width,↓reduceIte]
  unfold Usize.wrapping_shr UScalar.wrapping_shr
  rw [PV_CB3_WeightsMachine.cast_count n hn,Nat.mod_eq_of_lt width]

theorem left (x n : Usize) (hn : n.val < 32) :
    (x <<< n : Result Usize) = .ok (Usize.wrapping_shl x (UScalar.cast .U32 n)) := by
  have width : n.val < UScalarTy.numBits .Usize := lt_of_lt_of_le hn PV_CB3_WeightsMachine.width_min
  change UScalar.shiftLeft x n.val = _
  unfold UScalar.shiftLeft
  simp only [width,↓reduceIte]
  unfold Usize.wrapping_shl UScalar.wrapping_shl
  rw [PV_CB3_WeightsMachine.cast_count n hn,Nat.mod_eq_of_lt width]
#print axioms right
#print axioms left
end R1Z.PV_RunJoin_CheckedShift44
