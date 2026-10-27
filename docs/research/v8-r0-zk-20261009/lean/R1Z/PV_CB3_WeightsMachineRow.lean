import R1Z.PV_CB3_WeightsMachine
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsMachineRow
open Aeneas Aeneas.Std

def digit (j : Usize) (count : U32) : Usize := Usize.wrapping_shr j count &&& 3#usize

theorem or_value (a b : Usize) : (a ||| b).val = a.val ||| b.val := by
  change (a.bv ||| b.bv).toNat = _
  exact BitVec.toNat_or _ _

theorem digit_value (j : Usize) (count : U32) (hc : count.val < 10) :
    (digit j count).val = (j.val >>> count.val) &&& 3 := by
  change ((Usize.wrapping_shr j count).bv &&& (3#usize).bv).toNat = _
  rw [BitVec.toNat_and]
  change (Usize.wrapping_shr j count).val &&& 3 = _
  rw [PV_CB3_WeightsMachine.shift_right j count hc,Nat.shiftRight_eq_div_pow]

theorem digit_bound (j : Usize) (count : U32) (hc : count.val < 10) :
    (digit j count).val < 4 := by
  rw [digit_value j count hc]
  have h : (j.val >>> count.val) &&& 3 ≤ 3 := Nat.and_le_right
  omega

def row (j : Usize) : Usize :=
  ((((Usize.wrapping_shl (digit j 0#u32) 6#u32) |||
      (Usize.wrapping_shl (digit j 2#u32) 8#u32)) |||
      (Usize.wrapping_shl (digit j 4#u32) 4#u32)) ||| digit j 6#u32) |||
      (Usize.wrapping_shl (digit j 8#u32) 2#u32)

theorem row_value (j : Usize) : (row j).val = PV_CB3_WeightsBits.row j.val := by
  unfold row
  simp only [or_value]
  rw [PV_CB3_WeightsMachine.shift_left _ _ (digit_bound j 0#u32 (by decide)) (by decide),
    PV_CB3_WeightsMachine.shift_left _ _ (digit_bound j 2#u32 (by decide)) (by decide),
    PV_CB3_WeightsMachine.shift_left _ _ (digit_bound j 4#u32 (by decide)) (by decide),
    PV_CB3_WeightsMachine.shift_left _ _ (digit_bound j 8#u32 (by decide)) (by decide)]
  rw [digit_value j 0#u32 (by decide),digit_value j 2#u32 (by decide),
    digit_value j 4#u32 (by decide),digit_value j 6#u32 (by decide),digit_value j 8#u32 (by decide)]
  simp only [PV_CB3_WeightsBits.row,PV_CB3_WeightsBits.digit,Nat.shiftLeft_eq]
  have h0 : (0#u32).val = 0 := rfl
  have h2 : (2#u32).val = 2 := rfl
  have h4 : (4#u32).val = 4 := rfl
  have h6 : (6#u32).val = 6 := rfl
  have h8 : (8#u32).val = 8 := rfl
  simp only [h0,h2,h4,h6,h8,Nat.reduceMul]

/-- No restriction on j is needed for the two S permutation variants. -/
theorem row_bound (j : Usize) : (row j).val < 1024 := by
  rw [row_value]
  exact PV_CB3_WeightsBits.row_bound _
#print axioms or_value
#print axioms digit_value
#print axioms digit_bound
#print axioms row_value
#print axioms row_bound
end R1Z.PV_CB3_WeightsMachineRow
