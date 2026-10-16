import ExtractedMaskReducer
import ExtractedMaskCM31Mul
import ExtractedMaskM31AddSub

/-! Current extracted CM31.square word contract, following the checked
GeneratedCM31Square route over this extraction's actual field functions. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskCM31Square
open Aeneas.Std Result Error

abbrev P : Nat := AspisR1.ExtractedMaskM31AddSub.P
abbrev M31 := AspisR1SelectedMaskProbe.field.M31
abbrev CM := AspisR1SelectedMaskProbe.field.CM31

private theorem sourceP_value : AspisR1SelectedMaskProbe.field.P.val = P := by
  rw [AspisR1SelectedMaskProbe.field.P]
  rfl

private theorem widen_value (x : M31) :
    (Aeneas.Std.core.convert.num.FromU64U32.from x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  apply BitVec.toNat_setWidth_of_le
  decide

def squareOperand (a b : M31) : Result U64 := do
  let left ← UScalar.add
    (Aeneas.Std.core.convert.num.FromU64U32.from a)
    (Aeneas.Std.core.convert.num.FromU64U32.from b)
  let base ← UScalar.add
    (Aeneas.Std.core.convert.num.FromU64U32.from a)
    (Aeneas.Std.core.convert.num.FromU64U32.from
      AspisR1SelectedMaskProbe.field.P)
  let right ← UScalar.sub base
    (Aeneas.Std.core.convert.num.FromU64U32.from b)
  UScalar.mul left right

theorem squareOperand_success (a b : M31)
    (ha : a.val < P) (hb : b.val < P) :
    ∃ product : U64, squareOperand a b = .ok product ∧
      product.val = (a.val + b.val) * (a.val + P - b.val) := by
  have hP : P = 2147483647 := rfl
  have hleft : a.val + b.val < 2^32 := by omega
  obtain ⟨left, hl, hvl⟩ :=
    AspisR1.ExtractedMaskReducerOps.add_success
      (Aeneas.Std.core.convert.num.FromU64U32.from a)
      (Aeneas.Std.core.convert.num.FromU64U32.from b)
      (by
        rw [widen_value, widen_value]
        exact Nat.lt_trans hleft (by norm_num))
  rw [widen_value, widen_value] at hvl
  obtain ⟨base, hbase, hvbase⟩ :=
    AspisR1.ExtractedMaskReducerOps.add_success
      (Aeneas.Std.core.convert.num.FromU64U32.from a)
      (Aeneas.Std.core.convert.num.FromU64U32.from
        AspisR1SelectedMaskProbe.field.P)
      (by rw [widen_value, widen_value, sourceP_value]; omega)
  rw [widen_value, widen_value, sourceP_value] at hvbase
  obtain ⟨right, hr, hvr⟩ :=
    AspisR1.ExtractedMaskReducerOps.sub_success base
      (Aeneas.Std.core.convert.num.FromU64U32.from b)
      (by rw [hvbase, widen_value]; omega)
  rw [hvbase, widen_value] at hvr
  have hprod : left.val * right.val < 2^64 := by
    have hleft' : left.val < 2^32 := by rw [hvl]; omega
    have hright' : right.val < 2^32 := by rw [hvr]; omega
    calc
      left.val * right.val < 2^32 * 2^32 :=
        Nat.mul_lt_mul_of_lt_of_lt hleft' hright'
      _ = 2^64 := by norm_num
  obtain ⟨product, hp, hvp⟩ :=
    AspisR1.ExtractedMaskReducerOps.mul_success left right hprod
  refine ⟨product, ?_, ?_⟩
  · simp only [squareOperand, hl, hbase, hr, hp, bind_tc_ok]
  · simpa only [hvl, hvr] using hvp

theorem generated_square_graph (x : CM) :
    AspisR1SelectedMaskProbe.field.CM31.square x = (do
      let product ← squareOperand x.a x.b
      let real ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 product
      let ab ← AspisR1SelectedMaskProbe.field.M31.mul x.a x.b
      let imag ← AspisR1SelectedMaskProbe.field.M31.double ab
      Result.ok ⟨real, imag⟩) := by
  simp only [AspisR1SelectedMaskProbe.field.CM31.square,
    AspisR1SelectedMaskProbe.field.P, squareOperand,
    Aeneas.Std.lift, bind_tc_ok, bind_assoc_eq]
  rfl

theorem current_square_words (x : CM)
    (hx : AspisR1.ExtractedMaskTowerAdd.CanonicalCM x) :
    ∃ z : CM,
      AspisR1SelectedMaskProbe.field.CM31.square x = .ok z ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalCM z ∧
      z.a.val = ((x.a.val + x.b.val) *
        (x.a.val + P - x.b.val)) % P ∧
      z.b.val = ((x.a.val * x.b.val) % P +
        (x.a.val * x.b.val) % P) % P := by
  obtain ⟨product, hp, hvp⟩ := squareOperand_success x.a x.b hx.1 hx.2
  obtain ⟨real, hr, hvr, hcr⟩ :=
    AspisR1.ExtractedMaskReducer.current_wrapper_mod product
  obtain ⟨ab, hab, hvab, hcab⟩ :=
    AspisR1.ExtractedMaskReducer.current_mul_mod x.a x.b
  obtain ⟨imag, hi, hvi, hci⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod ab ab hcab hcab
  refine ⟨⟨real, imag⟩, ?_, ⟨hcr, hci⟩, ?_, ?_⟩
  · rw [generated_square_graph]
    simp only [hp, hr, hab, AspisR1SelectedMaskProbe.field.M31.double,
      hi, bind_tc_ok]
  · calc
      real.val = product.val % P := hvr
      _ = ((x.a.val + x.b.val) * (x.a.val + P - x.b.val)) % P := by
        rw [hvp]
  · rw [hvab] at hvi
    exact hvi

#print axioms squareOperand_success
#print axioms generated_square_graph
#print axioms current_square_words
end AspisR1.ExtractedMaskCM31Square
