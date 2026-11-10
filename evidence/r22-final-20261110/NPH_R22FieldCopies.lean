import NPH_R22FieldRef
import NHT_Constants
import NJS_Extract.Funs
import NMP_prepare.Funs
import NMT_tx1.Funs
import Op3I_Source
import S1NativeCompactModelV1
import SelectedWideViewFunsV1
import R22Stage2LeafTotal
import AspisR1BatchedWeightsExtraction.Funs
import AspisR1CurrentWide.Funs
import AspisR1Qm31ArithmeticProbe.Funs
import AspisR1SelectedMaskProbe.Funs
import AspisR1SemanticCallExtraction.Funs
import AspisR72Sampler.Funs
import AspisV8R19.ComplexFieldSlice
import AspisV8R19.GuardedFieldSlice
import AspisV8R19.QuarticFieldSlice
import NEI_LineFull.Funs
import RPu_FIq_Native01
import S8Kani2MutableSource
import S8OwnedP6.Funs

/-! NPH_ (R22 re-pin): every gate copy of the frozen M31 kernels that the
deployed_splitB cone reaches with a checked (overflow-checks ON) body is proved
definitionally equal to the NPH_R22FieldRef reference, and inherits its checked
totality on the stated domain and its R22 corollary (explicit operational tree, every
executed checked op safe, wrapping result = checked result). The guarded M31.mul
variant (AspisR72Sampler, AspisV8R19 slices: source blob with the r23 guard) is proved
TOTAL for every U32 pair directly. Standard axioms; no merged module is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22FieldCopies
open Aeneas Aeneas.Std Result AspisR1.R22TotalCheckedComposition AspisR1.NPH_R22FieldRef

theorem CW_reduce_u64_eq : AspisR1CurrentWide.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem CW_reduce_u64_R22 (x : U64) : ∃ y, AspisR1CurrentWide.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [CW_reduce_u64_eq]; exact reduce_R22 x

theorem QA_reduce_u64_eq : AspisR1Qm31ArithmeticProbe.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem QA_reduce_u64_R22 (x : U64) : ∃ y, AspisR1Qm31ArithmeticProbe.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [QA_reduce_u64_eq]; exact reduce_R22 x

theorem SM_reduce_u64_eq : AspisR1SelectedMaskProbe.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem SM_reduce_u64_R22 (x : U64) : ∃ y, AspisR1SelectedMaskProbe.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [SM_reduce_u64_eq]; exact reduce_R22 x

theorem SC_reduce_u64_eq : AspisR1SemanticCallExtraction.aspis_core.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem SC_reduce_u64_R22 (x : U64) : ∃ y, AspisR1SemanticCallExtraction.aspis_core.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [SC_reduce_u64_eq]; exact reduce_R22 x

theorem R72_reduce_u64_eq : AspisR72Sampler.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem R72_reduce_u64_R22 (x : U64) : ∃ y, AspisR72Sampler.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [R72_reduce_u64_eq]; exact reduce_R22 x

theorem R65_reduce_u64_eq : AspisR65Field.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem R65_reduce_u64_R22 (x : U64) : ∃ y, AspisR65Field.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [R65_reduce_u64_eq]; exact reduce_R22 x

theorem R64_reduce_u64_eq : AspisR64Field.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem R64_reduce_u64_R22 (x : U64) : ∃ y, AspisR64Field.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [R64_reduce_u64_eq]; exact reduce_R22 x

theorem R66_reduce_u64_eq : AspisR66Field.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem R66_reduce_u64_R22 (x : U64) : ∃ y, AspisR66Field.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [R66_reduce_u64_eq]; exact reduce_R22 x

theorem FIq_reduce_u64_eq : FIq_Native.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem FIq_reduce_u64_R22 (x : U64) : ∃ y, FIq_Native.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [FIq_reduce_u64_eq]; exact reduce_R22 x

theorem BW_reduce_u64_eq : AspisR1BatchedWeightsExtraction.aspis_core.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem BW_reduce_u64_R22 (x : U64) : ∃ y, AspisR1BatchedWeightsExtraction.aspis_core.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [BW_reduce_u64_eq]; exact reduce_R22 x

theorem S8K_reduce_u64_eq : S8Kani2MutableExtraction.aspis_core.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem S8K_reduce_u64_R22 (x : U64) : ∃ y, S8Kani2MutableExtraction.aspis_core.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [S8K_reduce_u64_eq]; exact reduce_R22 x

theorem NEI_reduce_u64_eq : NEI_LineFull.aspis_core.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem NEI_reduce_u64_R22 (x : U64) : ∃ y, NEI_LineFull.aspis_core.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [NEI_reduce_u64_eq]; exact reduce_R22 x

theorem S8O_reduce_u64_eq : S8OwnedP6.aspis_core.field.reduce_u64 = refReduce := by
  funext x; with_unfolding_all rfl

theorem S8O_reduce_u64_R22 (x : U64) : ∃ y, S8OwnedP6.aspis_core.field.reduce_u64 x = ok y ∧ y.val < 2147483647 ∧
    NoOverflow (reduceCode x) ∧ wrapping (reduceCode x) = ok y := by
  rw [S8O_reduce_u64_eq]; exact reduce_R22 x

theorem CW_M31_add_eq : AspisR1CurrentWide.field.M31.add = refAdd := by
  funext x y; with_unfolding_all rfl

theorem CW_M31_add_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR1CurrentWide.field.M31.add x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (addCode x y) ∧ wrapping (addCode x y) = ok z := by
  rw [CW_M31_add_eq]; exact add_R22 x y hx hy

theorem QA_M31_add_eq : AspisR1Qm31ArithmeticProbe.field.M31.add = refAdd := by
  funext x y; with_unfolding_all rfl

theorem QA_M31_add_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.M31.add x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (addCode x y) ∧ wrapping (addCode x y) = ok z := by
  rw [QA_M31_add_eq]; exact add_R22 x y hx hy

theorem SM_M31_add_eq : AspisR1SelectedMaskProbe.field.M31.add = refAdd := by
  funext x y; with_unfolding_all rfl

theorem SM_M31_add_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR1SelectedMaskProbe.field.M31.add x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (addCode x y) ∧ wrapping (addCode x y) = ok z := by
  rw [SM_M31_add_eq]; exact add_R22 x y hx hy

theorem SC_M31_add_eq : AspisR1SemanticCallExtraction.aspis_core.field.M31.add = refAdd := by
  funext x y; with_unfolding_all rfl

theorem SC_M31_add_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.M31.add x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (addCode x y) ∧ wrapping (addCode x y) = ok z := by
  rw [SC_M31_add_eq]; exact add_R22 x y hx hy

theorem R72_M31_add_eq : AspisR72Sampler.field.M31.add = refAdd := by
  funext x y; with_unfolding_all rfl

theorem R72_M31_add_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR72Sampler.field.M31.add x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (addCode x y) ∧ wrapping (addCode x y) = ok z := by
  rw [R72_M31_add_eq]; exact add_R22 x y hx hy

theorem R65_M31_add_eq : AspisR65Field.field.M31.add = refAdd := by
  funext x y; with_unfolding_all rfl

theorem R65_M31_add_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR65Field.field.M31.add x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (addCode x y) ∧ wrapping (addCode x y) = ok z := by
  rw [R65_M31_add_eq]; exact add_R22 x y hx hy

theorem R66_M31_add_eq : AspisR66Field.field.M31.add = refAdd := by
  funext x y; with_unfolding_all rfl

theorem R66_M31_add_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR66Field.field.M31.add x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (addCode x y) ∧ wrapping (addCode x y) = ok z := by
  rw [R66_M31_add_eq]; exact add_R22 x y hx hy

theorem FIq_M31_add_eq : FIq_Native.field.M31.add = refAdd := by
  funext x y; with_unfolding_all rfl

theorem FIq_M31_add_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, FIq_Native.field.M31.add x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (addCode x y) ∧ wrapping (addCode x y) = ok z := by
  rw [FIq_M31_add_eq]; exact add_R22 x y hx hy

theorem CW_M31_sub_eq : AspisR1CurrentWide.field.M31.sub = refSub := by
  funext x y; with_unfolding_all rfl

theorem CW_M31_sub_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR1CurrentWide.field.M31.sub x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (subCode x y) ∧ wrapping (subCode x y) = ok z := by
  rw [CW_M31_sub_eq]; exact sub_R22 x y hx hy

theorem QA_M31_sub_eq : AspisR1Qm31ArithmeticProbe.field.M31.sub = refSub := by
  funext x y; with_unfolding_all rfl

theorem QA_M31_sub_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.M31.sub x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (subCode x y) ∧ wrapping (subCode x y) = ok z := by
  rw [QA_M31_sub_eq]; exact sub_R22 x y hx hy

theorem SM_M31_sub_eq : AspisR1SelectedMaskProbe.field.M31.sub = refSub := by
  funext x y; with_unfolding_all rfl

theorem SM_M31_sub_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR1SelectedMaskProbe.field.M31.sub x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (subCode x y) ∧ wrapping (subCode x y) = ok z := by
  rw [SM_M31_sub_eq]; exact sub_R22 x y hx hy

theorem SC_M31_sub_eq : AspisR1SemanticCallExtraction.aspis_core.field.M31.sub = refSub := by
  funext x y; with_unfolding_all rfl

theorem SC_M31_sub_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.M31.sub x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (subCode x y) ∧ wrapping (subCode x y) = ok z := by
  rw [SC_M31_sub_eq]; exact sub_R22 x y hx hy

theorem R72_M31_sub_eq : AspisR72Sampler.field.M31.sub = refSub := by
  funext x y; with_unfolding_all rfl

theorem R72_M31_sub_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR72Sampler.field.M31.sub x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (subCode x y) ∧ wrapping (subCode x y) = ok z := by
  rw [R72_M31_sub_eq]; exact sub_R22 x y hx hy

theorem R66_M31_sub_eq : AspisR66Field.field.M31.sub = refSub := by
  funext x y; with_unfolding_all rfl

theorem R66_M31_sub_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, AspisR66Field.field.M31.sub x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (subCode x y) ∧ wrapping (subCode x y) = ok z := by
  rw [R66_M31_sub_eq]; exact sub_R22 x y hx hy

theorem FIq_M31_sub_eq : FIq_Native.field.M31.sub = refSub := by
  funext x y; with_unfolding_all rfl

theorem FIq_M31_sub_R22 (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, FIq_Native.field.M31.sub x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (subCode x y) ∧ wrapping (subCode x y) = ok z := by
  rw [FIq_M31_sub_eq]; exact sub_R22 x y hx hy

theorem CW_M31_mul_eq : AspisR1CurrentWide.field.M31.mul = refMul := by
  funext x y; with_unfolding_all rfl

theorem CW_M31_mul_R22 (x y : U32) : ∃ z, AspisR1CurrentWide.field.M31.mul x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (mulCode x y) ∧ wrapping (mulCode x y) = ok z := by
  rw [CW_M31_mul_eq]; exact mul_R22 x y

theorem QA_M31_mul_eq : AspisR1Qm31ArithmeticProbe.field.M31.mul = refMul := by
  funext x y; with_unfolding_all rfl

theorem QA_M31_mul_R22 (x y : U32) : ∃ z, AspisR1Qm31ArithmeticProbe.field.M31.mul x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (mulCode x y) ∧ wrapping (mulCode x y) = ok z := by
  rw [QA_M31_mul_eq]; exact mul_R22 x y

theorem SM_M31_mul_eq : AspisR1SelectedMaskProbe.field.M31.mul = refMul := by
  funext x y; with_unfolding_all rfl

theorem SM_M31_mul_R22 (x y : U32) : ∃ z, AspisR1SelectedMaskProbe.field.M31.mul x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (mulCode x y) ∧ wrapping (mulCode x y) = ok z := by
  rw [SM_M31_mul_eq]; exact mul_R22 x y

theorem SC_M31_mul_eq : AspisR1SemanticCallExtraction.aspis_core.field.M31.mul = refMul := by
  funext x y; with_unfolding_all rfl

theorem SC_M31_mul_R22 (x y : U32) : ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.M31.mul x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (mulCode x y) ∧ wrapping (mulCode x y) = ok z := by
  rw [SC_M31_mul_eq]; exact mul_R22 x y

theorem FIq_M31_mul_eq : FIq_Native.field.M31.mul = refMul := by
  funext x y; with_unfolding_all rfl

theorem FIq_M31_mul_R22 (x y : U32) : ∃ z, FIq_Native.field.M31.mul x y = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (mulCode x y) ∧ wrapping (mulCode x y) = ok z := by
  rw [FIq_M31_mul_eq]; exact mul_R22 x y

theorem SM_M31_neg_eq : AspisR1SelectedMaskProbe.field.M31.neg = refNeg := by
  funext x; with_unfolding_all rfl

theorem SM_M31_neg_R22 (x : U32) (hx : x.val ≤ 2147483647) : ∃ z, AspisR1SelectedMaskProbe.field.M31.neg x = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (negCode x) ∧ wrapping (negCode x) = ok z := by
  rw [SM_M31_neg_eq]; exact neg_R22 x hx

theorem R72_M31_neg_eq : AspisR72Sampler.field.M31.neg = refNeg := by
  funext x; with_unfolding_all rfl

theorem R72_M31_neg_R22 (x : U32) (hx : x.val ≤ 2147483647) : ∃ z, AspisR72Sampler.field.M31.neg x = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (negCode x) ∧ wrapping (negCode x) = ok z := by
  rw [R72_M31_neg_eq]; exact neg_R22 x hx

theorem R65_M31_neg_eq : AspisR65Field.field.M31.neg = refNeg := by
  funext x; with_unfolding_all rfl

theorem R65_M31_neg_R22 (x : U32) (hx : x.val ≤ 2147483647) : ∃ z, AspisR65Field.field.M31.neg x = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (negCode x) ∧ wrapping (negCode x) = ok z := by
  rw [R65_M31_neg_eq]; exact neg_R22 x hx

theorem R66_M31_neg_eq : AspisR66Field.field.M31.neg = refNeg := by
  funext x; with_unfolding_all rfl

theorem R66_M31_neg_R22 (x : U32) (hx : x.val ≤ 2147483647) : ∃ z, AspisR66Field.field.M31.neg x = ok z ∧ z.val < 2147483647 ∧
    NoOverflow (negCode x) ∧ wrapping (negCode x) = ok z := by
  rw [R66_M31_neg_eq]; exact neg_R22 x hx

/-! ### Guarded M31.mul variant (canonical fast path with `x >>> 31#i32`, raw fallback
through reduce_u64): TOTAL for every stored U32 pair. -/

theorem shr31i_val (x : U64) :
    ∃ z, (x >>> 31#i32 : Result U64) = ok z ∧ z.val = x.val / 2147483648 := by
  obtain ⟨z, hz, hv, _⟩ := WP.spec_imp_exists
    (UScalar.ShiftRight_IScalar_spec x 31#i32 (by decide) (by decide))
  refine ⟨z, hz, ?_⟩
  rw [hv, Nat.shiftRight_eq_div_pow]; rfl

theorem R72_M31_mul_total (x y : U32) : ∃ z, AspisR72Sampler.field.M31.mul x y = ok z ∧ z.val < 2147483647 := by
  have hP := P32_val
  have hPv : (AspisR72Sampler.field.P).val = 2147483647 := by unfold AspisR72Sampler.field.P; rfl
  have hx : x.val < 4294967296 := x.bv.isLt
  have hy : y.val < 4294967296 := y.bv.isLt
  have hm : x.val * y.val ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
  have hb : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val ≤ UScalar.max .U64 := by
    rw [cast64_val, cast64_val, max64]; omega
  obtain ⟨p, hp, vp⟩ := mul_ok _ _ hb
  have hred := R72_reduce_u64_eq
  obtain ⟨r, hr, vr⟩ := refReduce_total p
  by_cases hxc : x < AspisR72Sampler.field.P
  · by_cases hyc : y < AspisR72Sampler.field.P
    · have hxv : x.val < 2147483647 := by have := hxc; change x.val < (AspisR72Sampler.field.P).val at this; omega
      have hyv : y.val < 2147483647 := by have := hyc; change y.val < (AspisR72Sampler.field.P).val at this; omega
      have hm2 : x.val * y.val ≤ 2147483646 * 2147483646 := Nat.mul_le_mul (by omega) (by omega)
      rw [cast64_val, cast64_val] at vp
      obtain ⟨i4, h4, v4⟩ := shr31i_val p
      have hand : (p &&& UScalar.cast .U64 AspisR72Sampler.field.P).val ≤ 2147483647 := by
        rw [UScalar.val_and, cast64_val, hPv]; exact Nat.and_le_right
      have hs : (p &&& UScalar.cast .U64 AspisR72Sampler.field.P).val + i4.val ≤ UScalar.max .U64 := by
        rw [v4, max64]; omega
      obtain ⟨s, h5, v5⟩ := add_ok _ _ hs
      have sb : s.val < 2 * 2147483647 + 2147483647 := by rw [v5, v4, vp]; omega
      by_cases hge : s ≥ UScalar.cast .U64 AspisR72Sampler.field.P
      · have hgev : 2147483647 ≤ s.val := by
          have := hge; change (UScalar.cast .U64 AspisR72Sampler.field.P).val ≤ s.val at this; rw [cast64_val, hPv] at this; exact this
        obtain ⟨i7, h7, v7⟩ := sub_ok s (UScalar.cast .U64 AspisR72Sampler.field.P) (by rw [cast64_val, hPv]; exact hgev)
        have i7b : i7.val < 4294967296 := by rw [v7, cast64_val, hPv]; omega
        refine ⟨UScalar.cast .U32 i7, ?_, ?_⟩
        · simp only [AspisR72Sampler.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, h4, h5, hge, h7]
        · rw [cast32_val _ i7b, v7, cast64_val, hPv]
          have : s.val < 2 * 2147483647 := by
            rw [v5, v4, vp]
            have hq : x.val * y.val / 2147483648 ≤ 2147483646 := by omega
            omega
          omega
      · have hltv : s.val < 2147483647 := by
          have : ¬ ((UScalar.cast .U64 AspisR72Sampler.field.P).val ≤ s.val) := hge
          rw [cast64_val, hPv] at this; omega
        refine ⟨UScalar.cast .U32 s, ?_, by rw [cast32_val _ (by omega)]; exact hltv⟩
        simp only [AspisR72Sampler.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, h4, h5, hge]
    · refine ⟨r, ?_, vr⟩
      simp only [AspisR72Sampler.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, hred, hr]
  · refine ⟨r, ?_, vr⟩
    simp only [AspisR72Sampler.field.M31.mul, hxc, ↓reduceIte, lift, bind_tc_ok, hp, hred, hr]

theorem R65_M31_mul_total (x y : U32) : ∃ z, AspisR65Field.field.M31.mul x y = ok z ∧ z.val < 2147483647 := by
  have hP := P32_val
  have hPv : (AspisR65Field.field.P).val = 2147483647 := by unfold AspisR65Field.field.P; rfl
  have hx : x.val < 4294967296 := x.bv.isLt
  have hy : y.val < 4294967296 := y.bv.isLt
  have hm : x.val * y.val ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
  have hb : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val ≤ UScalar.max .U64 := by
    rw [cast64_val, cast64_val, max64]; omega
  obtain ⟨p, hp, vp⟩ := mul_ok _ _ hb
  have hred := R65_reduce_u64_eq
  obtain ⟨r, hr, vr⟩ := refReduce_total p
  by_cases hxc : x < AspisR65Field.field.P
  · by_cases hyc : y < AspisR65Field.field.P
    · have hxv : x.val < 2147483647 := by have := hxc; change x.val < (AspisR65Field.field.P).val at this; omega
      have hyv : y.val < 2147483647 := by have := hyc; change y.val < (AspisR65Field.field.P).val at this; omega
      have hm2 : x.val * y.val ≤ 2147483646 * 2147483646 := Nat.mul_le_mul (by omega) (by omega)
      rw [cast64_val, cast64_val] at vp
      obtain ⟨i4, h4, v4⟩ := shr31i_val p
      have hand : (p &&& UScalar.cast .U64 AspisR65Field.field.P).val ≤ 2147483647 := by
        rw [UScalar.val_and, cast64_val, hPv]; exact Nat.and_le_right
      have hs : (p &&& UScalar.cast .U64 AspisR65Field.field.P).val + i4.val ≤ UScalar.max .U64 := by
        rw [v4, max64]; omega
      obtain ⟨s, h5, v5⟩ := add_ok _ _ hs
      have sb : s.val < 2 * 2147483647 + 2147483647 := by rw [v5, v4, vp]; omega
      by_cases hge : s ≥ UScalar.cast .U64 AspisR65Field.field.P
      · have hgev : 2147483647 ≤ s.val := by
          have := hge; change (UScalar.cast .U64 AspisR65Field.field.P).val ≤ s.val at this; rw [cast64_val, hPv] at this; exact this
        obtain ⟨i7, h7, v7⟩ := sub_ok s (UScalar.cast .U64 AspisR65Field.field.P) (by rw [cast64_val, hPv]; exact hgev)
        have i7b : i7.val < 4294967296 := by rw [v7, cast64_val, hPv]; omega
        refine ⟨UScalar.cast .U32 i7, ?_, ?_⟩
        · simp only [AspisR65Field.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, h4, h5, hge, h7]
        · rw [cast32_val _ i7b, v7, cast64_val, hPv]
          have : s.val < 2 * 2147483647 := by
            rw [v5, v4, vp]
            have hq : x.val * y.val / 2147483648 ≤ 2147483646 := by omega
            omega
          omega
      · have hltv : s.val < 2147483647 := by
          have : ¬ ((UScalar.cast .U64 AspisR65Field.field.P).val ≤ s.val) := hge
          rw [cast64_val, hPv] at this; omega
        refine ⟨UScalar.cast .U32 s, ?_, by rw [cast32_val _ (by omega)]; exact hltv⟩
        simp only [AspisR65Field.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, h4, h5, hge]
    · refine ⟨r, ?_, vr⟩
      simp only [AspisR65Field.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, hred, hr]
  · refine ⟨r, ?_, vr⟩
    simp only [AspisR65Field.field.M31.mul, hxc, ↓reduceIte, lift, bind_tc_ok, hp, hred, hr]

theorem R64_M31_mul_total (x y : U32) : ∃ z, AspisR64Field.field.M31.mul x y = ok z ∧ z.val < 2147483647 := by
  have hP := P32_val
  have hPv : (AspisR64Field.field.P).val = 2147483647 := by unfold AspisR64Field.field.P; rfl
  have hx : x.val < 4294967296 := x.bv.isLt
  have hy : y.val < 4294967296 := y.bv.isLt
  have hm : x.val * y.val ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
  have hb : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val ≤ UScalar.max .U64 := by
    rw [cast64_val, cast64_val, max64]; omega
  obtain ⟨p, hp, vp⟩ := mul_ok _ _ hb
  have hred := R64_reduce_u64_eq
  obtain ⟨r, hr, vr⟩ := refReduce_total p
  by_cases hxc : x < AspisR64Field.field.P
  · by_cases hyc : y < AspisR64Field.field.P
    · have hxv : x.val < 2147483647 := by have := hxc; change x.val < (AspisR64Field.field.P).val at this; omega
      have hyv : y.val < 2147483647 := by have := hyc; change y.val < (AspisR64Field.field.P).val at this; omega
      have hm2 : x.val * y.val ≤ 2147483646 * 2147483646 := Nat.mul_le_mul (by omega) (by omega)
      rw [cast64_val, cast64_val] at vp
      obtain ⟨i4, h4, v4⟩ := shr31i_val p
      have hand : (p &&& UScalar.cast .U64 AspisR64Field.field.P).val ≤ 2147483647 := by
        rw [UScalar.val_and, cast64_val, hPv]; exact Nat.and_le_right
      have hs : (p &&& UScalar.cast .U64 AspisR64Field.field.P).val + i4.val ≤ UScalar.max .U64 := by
        rw [v4, max64]; omega
      obtain ⟨s, h5, v5⟩ := add_ok _ _ hs
      have sb : s.val < 2 * 2147483647 + 2147483647 := by rw [v5, v4, vp]; omega
      by_cases hge : s ≥ UScalar.cast .U64 AspisR64Field.field.P
      · have hgev : 2147483647 ≤ s.val := by
          have := hge; change (UScalar.cast .U64 AspisR64Field.field.P).val ≤ s.val at this; rw [cast64_val, hPv] at this; exact this
        obtain ⟨i7, h7, v7⟩ := sub_ok s (UScalar.cast .U64 AspisR64Field.field.P) (by rw [cast64_val, hPv]; exact hgev)
        have i7b : i7.val < 4294967296 := by rw [v7, cast64_val, hPv]; omega
        refine ⟨UScalar.cast .U32 i7, ?_, ?_⟩
        · simp only [AspisR64Field.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, h4, h5, hge, h7]
        · rw [cast32_val _ i7b, v7, cast64_val, hPv]
          have : s.val < 2 * 2147483647 := by
            rw [v5, v4, vp]
            have hq : x.val * y.val / 2147483648 ≤ 2147483646 := by omega
            omega
          omega
      · have hltv : s.val < 2147483647 := by
          have : ¬ ((UScalar.cast .U64 AspisR64Field.field.P).val ≤ s.val) := hge
          rw [cast64_val, hPv] at this; omega
        refine ⟨UScalar.cast .U32 s, ?_, by rw [cast32_val _ (by omega)]; exact hltv⟩
        simp only [AspisR64Field.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, h4, h5, hge]
    · refine ⟨r, ?_, vr⟩
      simp only [AspisR64Field.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, hred, hr]
  · refine ⟨r, ?_, vr⟩
    simp only [AspisR64Field.field.M31.mul, hxc, ↓reduceIte, lift, bind_tc_ok, hp, hred, hr]

theorem R66_M31_mul_total (x y : U32) : ∃ z, AspisR66Field.field.M31.mul x y = ok z ∧ z.val < 2147483647 := by
  have hP := P32_val
  have hPv : (AspisR66Field.field.P).val = 2147483647 := by unfold AspisR66Field.field.P; rfl
  have hx : x.val < 4294967296 := x.bv.isLt
  have hy : y.val < 4294967296 := y.bv.isLt
  have hm : x.val * y.val ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
  have hb : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val ≤ UScalar.max .U64 := by
    rw [cast64_val, cast64_val, max64]; omega
  obtain ⟨p, hp, vp⟩ := mul_ok _ _ hb
  have hred := R66_reduce_u64_eq
  obtain ⟨r, hr, vr⟩ := refReduce_total p
  by_cases hxc : x < AspisR66Field.field.P
  · by_cases hyc : y < AspisR66Field.field.P
    · have hxv : x.val < 2147483647 := by have := hxc; change x.val < (AspisR66Field.field.P).val at this; omega
      have hyv : y.val < 2147483647 := by have := hyc; change y.val < (AspisR66Field.field.P).val at this; omega
      have hm2 : x.val * y.val ≤ 2147483646 * 2147483646 := Nat.mul_le_mul (by omega) (by omega)
      rw [cast64_val, cast64_val] at vp
      obtain ⟨i4, h4, v4⟩ := shr31i_val p
      have hand : (p &&& UScalar.cast .U64 AspisR66Field.field.P).val ≤ 2147483647 := by
        rw [UScalar.val_and, cast64_val, hPv]; exact Nat.and_le_right
      have hs : (p &&& UScalar.cast .U64 AspisR66Field.field.P).val + i4.val ≤ UScalar.max .U64 := by
        rw [v4, max64]; omega
      obtain ⟨s, h5, v5⟩ := add_ok _ _ hs
      have sb : s.val < 2 * 2147483647 + 2147483647 := by rw [v5, v4, vp]; omega
      by_cases hge : s ≥ UScalar.cast .U64 AspisR66Field.field.P
      · have hgev : 2147483647 ≤ s.val := by
          have := hge; change (UScalar.cast .U64 AspisR66Field.field.P).val ≤ s.val at this; rw [cast64_val, hPv] at this; exact this
        obtain ⟨i7, h7, v7⟩ := sub_ok s (UScalar.cast .U64 AspisR66Field.field.P) (by rw [cast64_val, hPv]; exact hgev)
        have i7b : i7.val < 4294967296 := by rw [v7, cast64_val, hPv]; omega
        refine ⟨UScalar.cast .U32 i7, ?_, ?_⟩
        · simp only [AspisR66Field.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, h4, h5, hge, h7]
        · rw [cast32_val _ i7b, v7, cast64_val, hPv]
          have : s.val < 2 * 2147483647 := by
            rw [v5, v4, vp]
            have hq : x.val * y.val / 2147483648 ≤ 2147483646 := by omega
            omega
          omega
      · have hltv : s.val < 2147483647 := by
          have : ¬ ((UScalar.cast .U64 AspisR66Field.field.P).val ≤ s.val) := hge
          rw [cast64_val, hPv] at this; omega
        refine ⟨UScalar.cast .U32 s, ?_, by rw [cast32_val _ (by omega)]; exact hltv⟩
        simp only [AspisR66Field.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, h4, h5, hge]
    · refine ⟨r, ?_, vr⟩
      simp only [AspisR66Field.field.M31.mul, hxc, hyc, ↓reduceIte, lift, bind_tc_ok, hp, hred, hr]
  · refine ⟨r, ?_, vr⟩
    simp only [AspisR66Field.field.M31.mul, hxc, ↓reduceIte, lift, bind_tc_ok, hp, hred, hr]

/-! ### Usize layout constants: TOTAL (no input). Each module's constant is
definitionally the 2021 AspisR1Stage2 constant whose checked value R22Stage2LeafTotal proved. -/

theorem C_NHT_Constants_compact_COMPACT_SEMANTIC_total : NHT_Constants.compact.COMPACT_SEMANTIC = ok 7015#usize :=
  (show NHT_Constants.compact.COMPACT_SEMANTIC = AspisR1Stage2.compact.COMPACT_SEMANTIC by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_COMPACT_SEMANTIC_total

theorem C_NHT_Constants_compact_OFF_OPENINGS_total : NHT_Constants.compact.OFF_OPENINGS = ok 10055#usize :=
  (show NHT_Constants.compact.OFF_OPENINGS = AspisR1Stage2.compact.OFF_OPENINGS by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_OFF_OPENINGS_total

theorem C_NHT_Constants_compact_SEMANTIC_COMPACT_VALUES_total : NHT_Constants.compact.SEMANTIC_COMPACT_VALUES = ok 426#usize :=
  (show NHT_Constants.compact.SEMANTIC_COMPACT_VALUES = AspisR1Stage2.compact.SEMANTIC_COMPACT_VALUES by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_SEMANTIC_COMPACT_VALUES_total

theorem C_NHT_Constants_verifier_SEMANTIC_BYTES_total : NHT_Constants.verifier.SEMANTIC_BYTES = ok 13831#usize :=
  (show NHT_Constants.verifier.SEMANTIC_BYTES = AspisR1Stage2.verifier.SEMANTIC_BYTES by with_unfolding_all rfl).trans AspisR1Stage2.r22_verifier_SEMANTIC_BYTES_total

theorem C_NJS_Extract_compact_COMPACT_SEMANTIC_total : NJS_Extract.compact.COMPACT_SEMANTIC = ok 7015#usize :=
  (show NJS_Extract.compact.COMPACT_SEMANTIC = AspisR1Stage2.compact.COMPACT_SEMANTIC by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_COMPACT_SEMANTIC_total

theorem C_NJS_Extract_compact_MAX_NODES_total : NJS_Extract.compact.MAX_NODES = ok 914#usize :=
  (show NJS_Extract.compact.MAX_NODES = AspisR1Stage2.compact.MAX_NODES by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_MAX_NODES_total

theorem C_NJS_Extract_compact_MAX_PROOF_total : NJS_Extract.compact.MAX_PROOF = ok 57607#usize :=
  (show NJS_Extract.compact.MAX_PROOF = AspisR1Stage2.compact.MAX_PROOF by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_MAX_PROOF_total

theorem C_NJS_Extract_compact_OFF_NODES_total : NJS_Extract.compact.OFF_NODES = ok 28359#usize :=
  (show NJS_Extract.compact.OFF_NODES = AspisR1Stage2.compact.OFF_NODES by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_OFF_NODES_total

theorem C_NJS_Extract_compact_OFF_OPENINGS_total : NJS_Extract.compact.OFF_OPENINGS = ok 10055#usize :=
  (show NJS_Extract.compact.OFF_OPENINGS = AspisR1Stage2.compact.OFF_OPENINGS by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_OFF_OPENINGS_total

theorem C_NJS_Extract_compact_OPENING_total : NJS_Extract.compact.OPENING = ok 832#usize :=
  (show NJS_Extract.compact.OPENING = AspisR1Stage2.compact.OPENING by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_OPENING_total

theorem C_NJS_Extract_compact_SEMANTIC_COMPACT_VALUES_total : NJS_Extract.compact.SEMANTIC_COMPACT_VALUES = ok 426#usize :=
  (show NJS_Extract.compact.SEMANTIC_COMPACT_VALUES = AspisR1Stage2.compact.SEMANTIC_COMPACT_VALUES by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_SEMANTIC_COMPACT_VALUES_total

theorem C_NJS_Extract_verifier_SEMANTIC_BYTES_total : NJS_Extract.verifier.SEMANTIC_BYTES = ok 13831#usize :=
  (show NJS_Extract.verifier.SEMANTIC_BYTES = AspisR1Stage2.verifier.SEMANTIC_BYTES by with_unfolding_all rfl).trans AspisR1Stage2.r22_verifier_SEMANTIC_BYTES_total

theorem C_NMP_prepare_compact_COMPACT_SEMANTIC_total : NMP_prepare.compact.COMPACT_SEMANTIC = ok 7015#usize :=
  (show NMP_prepare.compact.COMPACT_SEMANTIC = AspisR1Stage2.compact.COMPACT_SEMANTIC by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_COMPACT_SEMANTIC_total

theorem C_NMP_prepare_compact_SEMANTIC_COMPACT_VALUES_total : NMP_prepare.compact.SEMANTIC_COMPACT_VALUES = ok 426#usize :=
  (show NMP_prepare.compact.SEMANTIC_COMPACT_VALUES = AspisR1Stage2.compact.SEMANTIC_COMPACT_VALUES by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_SEMANTIC_COMPACT_VALUES_total

theorem C_NMP_prepare_verifier_SEMANTIC_BYTES_total : NMP_prepare.verifier.SEMANTIC_BYTES = ok 13831#usize :=
  (show NMP_prepare.verifier.SEMANTIC_BYTES = AspisR1Stage2.verifier.SEMANTIC_BYTES by with_unfolding_all rfl).trans AspisR1Stage2.r22_verifier_SEMANTIC_BYTES_total

theorem C_NMT_tx1_compact_COMPACT_SEMANTIC_total : NMT_tx1.compact.COMPACT_SEMANTIC = ok 7015#usize :=
  (show NMT_tx1.compact.COMPACT_SEMANTIC = AspisR1Stage2.compact.COMPACT_SEMANTIC by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_COMPACT_SEMANTIC_total

theorem C_NMT_tx1_compact_SEMANTIC_COMPACT_VALUES_total : NMT_tx1.compact.SEMANTIC_COMPACT_VALUES = ok 426#usize :=
  (show NMT_tx1.compact.SEMANTIC_COMPACT_VALUES = AspisR1Stage2.compact.SEMANTIC_COMPACT_VALUES by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_SEMANTIC_COMPACT_VALUES_total

theorem C_NMT_tx1_verifier_SEMANTIC_BYTES_total : NMT_tx1.verifier.SEMANTIC_BYTES = ok 13831#usize :=
  (show NMT_tx1.verifier.SEMANTIC_BYTES = AspisR1Stage2.verifier.SEMANTIC_BYTES by with_unfolding_all rfl).trans AspisR1Stage2.r22_verifier_SEMANTIC_BYTES_total

theorem C_Op3I_Source_compact_COMPACT_SEMANTIC_total : Op3I_Source.compact.COMPACT_SEMANTIC = ok 7015#usize :=
  (show Op3I_Source.compact.COMPACT_SEMANTIC = AspisR1Stage2.compact.COMPACT_SEMANTIC by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_COMPACT_SEMANTIC_total

theorem C_Op3I_Source_compact_MAX_NODES_total : Op3I_Source.compact.MAX_NODES = ok 914#usize :=
  (show Op3I_Source.compact.MAX_NODES = AspisR1Stage2.compact.MAX_NODES by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_MAX_NODES_total

theorem C_Op3I_Source_compact_MAX_PROOF_total : Op3I_Source.compact.MAX_PROOF = ok 57607#usize :=
  (show Op3I_Source.compact.MAX_PROOF = AspisR1Stage2.compact.MAX_PROOF by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_MAX_PROOF_total

theorem C_Op3I_Source_compact_OFF_NODES_total : Op3I_Source.compact.OFF_NODES = ok 28359#usize :=
  (show Op3I_Source.compact.OFF_NODES = AspisR1Stage2.compact.OFF_NODES by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_OFF_NODES_total

theorem C_Op3I_Source_compact_OFF_OPENINGS_total : Op3I_Source.compact.OFF_OPENINGS = ok 10055#usize :=
  (show Op3I_Source.compact.OFF_OPENINGS = AspisR1Stage2.compact.OFF_OPENINGS by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_OFF_OPENINGS_total

theorem C_Op3I_Source_compact_OPENING_total : Op3I_Source.compact.OPENING = ok 832#usize :=
  (show Op3I_Source.compact.OPENING = AspisR1Stage2.compact.OPENING by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_OPENING_total

theorem C_Op3I_Source_compact_SEMANTIC_COMPACT_VALUES_total : Op3I_Source.compact.SEMANTIC_COMPACT_VALUES = ok 426#usize :=
  (show Op3I_Source.compact.SEMANTIC_COMPACT_VALUES = AspisR1Stage2.compact.SEMANTIC_COMPACT_VALUES by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_SEMANTIC_COMPACT_VALUES_total

theorem C_Op3I_Source_verifier_SEMANTIC_BYTES_total : Op3I_Source.verifier.SEMANTIC_BYTES = ok 13831#usize :=
  (show Op3I_Source.verifier.SEMANTIC_BYTES = AspisR1Stage2.verifier.SEMANTIC_BYTES by with_unfolding_all rfl).trans AspisR1Stage2.r22_verifier_SEMANTIC_BYTES_total

theorem C_AspisS1NativeCompact_compact_COMPACT_SEMANTIC_total : AspisS1NativeCompact.compact.COMPACT_SEMANTIC = ok 7015#usize :=
  (show AspisS1NativeCompact.compact.COMPACT_SEMANTIC = AspisR1Stage2.compact.COMPACT_SEMANTIC by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_COMPACT_SEMANTIC_total

theorem C_AspisS1NativeCompact_compact_SEMANTIC_COMPACT_VALUES_total : AspisS1NativeCompact.compact.SEMANTIC_COMPACT_VALUES = ok 426#usize :=
  (show AspisS1NativeCompact.compact.SEMANTIC_COMPACT_VALUES = AspisR1Stage2.compact.SEMANTIC_COMPACT_VALUES by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_SEMANTIC_COMPACT_VALUES_total

theorem C_AspisS1NativeCompact_verifier_SEMANTIC_BYTES_total : AspisS1NativeCompact.verifier.SEMANTIC_BYTES = ok 13831#usize :=
  (show AspisS1NativeCompact.verifier.SEMANTIC_BYTES = AspisR1Stage2.verifier.SEMANTIC_BYTES by with_unfolding_all rfl).trans AspisR1Stage2.r22_verifier_SEMANTIC_BYTES_total

theorem C_AspisR1SelectedWideViewV1_compact_COMPACT_SEMANTIC_total : AspisR1SelectedWideViewV1.compact.COMPACT_SEMANTIC = ok 7015#usize :=
  (show AspisR1SelectedWideViewV1.compact.COMPACT_SEMANTIC = AspisR1Stage2.compact.COMPACT_SEMANTIC by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_COMPACT_SEMANTIC_total

theorem C_AspisR1SelectedWideViewV1_compact_OFF_OPENINGS_total : AspisR1SelectedWideViewV1.compact.OFF_OPENINGS = ok 10055#usize :=
  (show AspisR1SelectedWideViewV1.compact.OFF_OPENINGS = AspisR1Stage2.compact.OFF_OPENINGS by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_OFF_OPENINGS_total

theorem C_AspisR1SelectedWideViewV1_compact_SEMANTIC_COMPACT_VALUES_total : AspisR1SelectedWideViewV1.compact.SEMANTIC_COMPACT_VALUES = ok 426#usize :=
  (show AspisR1SelectedWideViewV1.compact.SEMANTIC_COMPACT_VALUES = AspisR1Stage2.compact.SEMANTIC_COMPACT_VALUES by with_unfolding_all rfl).trans AspisR1Stage2.r22_compact_SEMANTIC_COMPACT_VALUES_total

theorem C_AspisR1SelectedWideViewV1_verifier_SEMANTIC_BYTES_total : AspisR1SelectedWideViewV1.verifier.SEMANTIC_BYTES = ok 13831#usize :=
  (show AspisR1SelectedWideViewV1.verifier.SEMANTIC_BYTES = AspisR1Stage2.verifier.SEMANTIC_BYTES by with_unfolding_all rfl).trans AspisR1Stage2.r22_verifier_SEMANTIC_BYTES_total

#print axioms CW_reduce_u64_eq
#print axioms CW_reduce_u64_R22
#print axioms QA_reduce_u64_eq
#print axioms QA_reduce_u64_R22
#print axioms SM_reduce_u64_eq
#print axioms SM_reduce_u64_R22
#print axioms SC_reduce_u64_eq
#print axioms SC_reduce_u64_R22
#print axioms R72_reduce_u64_eq
#print axioms R72_reduce_u64_R22
#print axioms R65_reduce_u64_eq
#print axioms R65_reduce_u64_R22
#print axioms R64_reduce_u64_eq
#print axioms R64_reduce_u64_R22
#print axioms R66_reduce_u64_eq
#print axioms R66_reduce_u64_R22
#print axioms FIq_reduce_u64_eq
#print axioms FIq_reduce_u64_R22
#print axioms BW_reduce_u64_eq
#print axioms BW_reduce_u64_R22
#print axioms S8K_reduce_u64_eq
#print axioms S8K_reduce_u64_R22
#print axioms NEI_reduce_u64_eq
#print axioms NEI_reduce_u64_R22
#print axioms S8O_reduce_u64_eq
#print axioms S8O_reduce_u64_R22
#print axioms CW_M31_add_eq
#print axioms CW_M31_add_R22
#print axioms QA_M31_add_eq
#print axioms QA_M31_add_R22
#print axioms SM_M31_add_eq
#print axioms SM_M31_add_R22
#print axioms SC_M31_add_eq
#print axioms SC_M31_add_R22
#print axioms R72_M31_add_eq
#print axioms R72_M31_add_R22
#print axioms R65_M31_add_eq
#print axioms R65_M31_add_R22
#print axioms R66_M31_add_eq
#print axioms R66_M31_add_R22
#print axioms FIq_M31_add_eq
#print axioms FIq_M31_add_R22
#print axioms CW_M31_sub_eq
#print axioms CW_M31_sub_R22
#print axioms QA_M31_sub_eq
#print axioms QA_M31_sub_R22
#print axioms SM_M31_sub_eq
#print axioms SM_M31_sub_R22
#print axioms SC_M31_sub_eq
#print axioms SC_M31_sub_R22
#print axioms R72_M31_sub_eq
#print axioms R72_M31_sub_R22
#print axioms R66_M31_sub_eq
#print axioms R66_M31_sub_R22
#print axioms FIq_M31_sub_eq
#print axioms FIq_M31_sub_R22
#print axioms CW_M31_mul_eq
#print axioms CW_M31_mul_R22
#print axioms QA_M31_mul_eq
#print axioms QA_M31_mul_R22
#print axioms SM_M31_mul_eq
#print axioms SM_M31_mul_R22
#print axioms SC_M31_mul_eq
#print axioms SC_M31_mul_R22
#print axioms FIq_M31_mul_eq
#print axioms FIq_M31_mul_R22
#print axioms SM_M31_neg_eq
#print axioms SM_M31_neg_R22
#print axioms R72_M31_neg_eq
#print axioms R72_M31_neg_R22
#print axioms R65_M31_neg_eq
#print axioms R65_M31_neg_R22
#print axioms R66_M31_neg_eq
#print axioms R66_M31_neg_R22
#print axioms R72_M31_mul_total
#print axioms R65_M31_mul_total
#print axioms R64_M31_mul_total
#print axioms R66_M31_mul_total
#print axioms C_NHT_Constants_compact_COMPACT_SEMANTIC_total
#print axioms C_NHT_Constants_compact_OFF_OPENINGS_total
#print axioms C_NHT_Constants_compact_SEMANTIC_COMPACT_VALUES_total
#print axioms C_NHT_Constants_verifier_SEMANTIC_BYTES_total
#print axioms C_NJS_Extract_compact_COMPACT_SEMANTIC_total
#print axioms C_NJS_Extract_compact_MAX_NODES_total
#print axioms C_NJS_Extract_compact_MAX_PROOF_total
#print axioms C_NJS_Extract_compact_OFF_NODES_total
#print axioms C_NJS_Extract_compact_OFF_OPENINGS_total
#print axioms C_NJS_Extract_compact_OPENING_total
#print axioms C_NJS_Extract_compact_SEMANTIC_COMPACT_VALUES_total
#print axioms C_NJS_Extract_verifier_SEMANTIC_BYTES_total
#print axioms C_NMP_prepare_compact_COMPACT_SEMANTIC_total
#print axioms C_NMP_prepare_compact_SEMANTIC_COMPACT_VALUES_total
#print axioms C_NMP_prepare_verifier_SEMANTIC_BYTES_total
#print axioms C_NMT_tx1_compact_COMPACT_SEMANTIC_total
#print axioms C_NMT_tx1_compact_SEMANTIC_COMPACT_VALUES_total
#print axioms C_NMT_tx1_verifier_SEMANTIC_BYTES_total
#print axioms C_Op3I_Source_compact_COMPACT_SEMANTIC_total
#print axioms C_Op3I_Source_compact_MAX_NODES_total
#print axioms C_Op3I_Source_compact_MAX_PROOF_total
#print axioms C_Op3I_Source_compact_OFF_NODES_total
#print axioms C_Op3I_Source_compact_OFF_OPENINGS_total
#print axioms C_Op3I_Source_compact_OPENING_total
#print axioms C_Op3I_Source_compact_SEMANTIC_COMPACT_VALUES_total
#print axioms C_Op3I_Source_verifier_SEMANTIC_BYTES_total
#print axioms C_AspisS1NativeCompact_compact_COMPACT_SEMANTIC_total
#print axioms C_AspisS1NativeCompact_compact_SEMANTIC_COMPACT_VALUES_total
#print axioms C_AspisS1NativeCompact_verifier_SEMANTIC_BYTES_total
#print axioms C_AspisR1SelectedWideViewV1_compact_COMPACT_SEMANTIC_total
#print axioms C_AspisR1SelectedWideViewV1_compact_OFF_OPENINGS_total
#print axioms C_AspisR1SelectedWideViewV1_compact_SEMANTIC_COMPACT_VALUES_total
#print axioms C_AspisR1SelectedWideViewV1_verifier_SEMANTIC_BYTES_total
end AspisR1.NPH_R22FieldCopies