import AspisR1S9SquareMulQMCutV1.Funs
import ExtractedMaskCM31Square
import S9SquareWrapCheckedV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualCMSquareOperandMapV1

abbrev ActualM31 := AspisR1S9SquareMulQMCutV1.field.M31
abbrev U64 := Std.U64
abbrev SelectedM31 := AspisR1SelectedMaskProbe.field.M31

def actualSquareOperand (a b : ActualM31) : Result U64 := do
  let a64 ← lift (core.convert.num.FromU64U32.from a)
  let b64 ← lift (core.convert.num.FromU64U32.from b)
  let left ← lift (Std.U64.wrapping_add a64 b64)
  let a64' ← lift (core.convert.num.FromU64U32.from a)
  let p64 ← lift (core.convert.num.FromU64U32.from AspisR1S9SquareMulQMCutV1.field.P)
  let base ← lift (Std.U64.wrapping_add a64' p64)
  let b64' ← lift (core.convert.num.FromU64U32.from b)
  let right ← lift (Std.U64.wrapping_sub base b64')
  lift (Std.U64.wrapping_mul left right)

private theorem widen_val (x : Std.U32) :
    (core.convert.num.FromU64U32.from x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  exact BitVec.toNat_setWidth_of_le (by decide)

private theorem sub64_val_of_le (x y : Std.U64) (h : y.val ≤ x.val) :
    (Std.U64.wrapping_sub x y).val = x.val - y.val := by
  rw [Std.U64.wrapping_sub_val_eq]
  have hy : y.val < 2^64 := y.bv.isLt
  have hx : x.val < 2^64 := x.bv.isLt
  have he : x.val + (2^64-y.val) = (x.val-y.val)+2^64 := by omega
  simp only [UScalar.size, UScalarTy.U64_numBits_eq]
  change (x.val + (2^64-y.val)) % 2^64 = x.val-y.val
  rw [he, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

private theorem selectedP_value :
    AspisR1SelectedMaskProbe.field.P.val = 2147483647 := by
  rw [AspisR1SelectedMaskProbe.field.P]
  rfl

private theorem actualP_eq_selectedP :
    AspisR1S9SquareMulQMCutV1.field.P.val =
      AspisR1SelectedMaskProbe.field.P.val := by
  rw [AspisR1S9SquareMulQMCutV1.field.P, selectedP_value]
  rfl

/-- The source-cut wrapping operand calculation is the same product as the
selected checked operand when both coordinates are canonical. -/
theorem actual_square_operand_eq_selected (a b : Std.U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    actualSquareOperand a b =
      AspisR1.ExtractedMaskCM31Square.squareOperand a b := by
  let a64 := core.convert.num.FromU64U32.from a
  let b64 := core.convert.num.FromU64U32.from b
  let p64 := core.convert.num.FromU64U32.from AspisR1S9SquareMulQMCutV1.field.P
  let left := Std.U64.wrapping_add a64 b64
  let base := Std.U64.wrapping_add a64 p64
  let right := Std.U64.wrapping_sub base b64
  let product := Std.U64.wrapping_mul left right
  have hP : AspisR1S9SquareMulQMCutV1.field.P.val = 2147483647 := by
    rw [actualP_eq_selectedP, selectedP_value]
  have hav : a64.val = a.val := by dsimp [a64]; exact widen_val a
  have hbv : b64.val = b.val := by dsimp [b64]; exact widen_val b
  have hpv : p64.val = 2147483647 := by
    dsimp [p64]
    rw [widen_val, hP]
  have hleft : left.val = a.val + b.val := by
    dsimp only [left]
    rw [Std.U64.wrapping_add_val_eq, hav, hbv]
    simp only [UScalar.size, UScalarTy.U64_numBits_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have hbase : base.val = a.val + 2147483647 := by
    dsimp only [base]
    rw [Std.U64.wrapping_add_val_eq, hav, hpv]
    simp only [UScalar.size, UScalarTy.U64_numBits_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have hright : right.val = a.val + 2147483647 - b.val := by
    dsimp only [right]
    rw [sub64_val_of_le base b64 (by rw [hbase, hbv]; omega), hbase, hbv]
  have hprodBound : left.val * right.val < 2^64 := by
    rw [hleft, hright]
    have hL : a.val+b.val < 2^32 := by omega
    have hR : a.val+2147483647-b.val < 2^32 := by omega
    calc
      (a.val+b.val)*(a.val+2147483647-b.val) < 2^32*2^32 :=
        Nat.mul_lt_mul_of_lt_of_lt hL hR
      _ = 2^64 := by norm_num
  have hproduct : product.val =
      (a.val+b.val)*(a.val+2147483647-b.val) := by
    dsimp only [product]
    rw [Std.U64.wrapping_mul_val_eq, hleft, hright]
    simp only [UScalar.size, UScalarTy.U64_numBits_eq]
    exact Nat.mod_eq_of_lt (by
      have hL : a.val+b.val < 2^32 := by omega
      have hR : a.val+2147483647-b.val < 2^32 := by omega
      calc
        (a.val+b.val)*(a.val+2147483647-b.val) < 2^32*2^32 :=
          Nat.mul_lt_mul_of_lt_of_lt hL hR
        _ = 2^64 := by norm_num)
  have hactual : actualSquareOperand a b = .ok product := by
    simp only [actualSquareOperand, lift, bind_tc_ok]
    rfl
  obtain ⟨selected, hselected, hselectedVal⟩ :=
    AspisR1.ExtractedMaskCM31Square.squareOperand_success a b ha hb
  have heq : product = selected :=
    UScalar.val_eq_imp product selected (hproduct.trans hselectedVal.symm)
  rw [hactual, hselected, heq]

#print axioms actual_square_operand_eq_selected

end AspisR1S9ActualCMSquareOperandMapV1
