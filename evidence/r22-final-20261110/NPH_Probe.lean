import R22TotalCheckedComposition
import AspisR1CurrentWide.Funs
import AspisR1Qm31ArithmeticProbe.Funs
/-! NPH_ API probe (diagnostic only, never credited): exact spec-lemma signatures of the
pinned Aeneas Std, and whether two gate field copies are definitionally equal. -/
open Aeneas Aeneas.Std Result
#check @UScalar.add_spec
#check @UScalar.sub_spec
#check @UScalar.mul_spec
#check @UScalar.ShiftRight_spec
#check @UScalar.ShiftRight_IScalar_spec
#check @Usize.ShiftRight_IScalar_spec
#check @UScalar.and_spec
#check @UScalar.cast_inBounds_spec
#check @WP.spec_imp_exists
#check @UScalar.add_equiv
#check @UScalar.sub_equiv
#check @UScalar.mul_equiv
#check @UScalar.wrapping_add
#check @UScalar.shiftRight
#check @UScalar.val_and
#check @UScalar.max_USize_eq
#check @core.convert.num.FromU64U32.from
#check @core.num.U64.wrapping_add
#print AspisR1CurrentWide.field.P
#print AspisR1CurrentWide.field.M31
#print AspisR1CurrentWide.field.CM31
example : AspisR1CurrentWide.field.M31.add = AspisR1Qm31ArithmeticProbe.field.M31.add := by
  funext x y; rfl
example : AspisR1CurrentWide.field.reduce_u64 = AspisR1Qm31ArithmeticProbe.field.reduce_u64 := by
  funext x; rfl
example (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR1CurrentWide.field.M31.add x y = ok z := by
  unfold AspisR1CurrentWide.field.M31.add
  progress as ⟨s, hs⟩
  · simp [AspisR1CurrentWide.field.P] at *
    split <;> sorry
