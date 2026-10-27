import ExtractedMaskReducerOps
import Mathlib.Data.Nat.Bitwise

/-! Checked source shift/mask/cast and one-minus-bit used by link_weight.
Reuse existing unsigned-scalar and narrowing lemmas; no generated data. -/
set_option autoImplicit false
namespace AspisR1.CopyLinkBitArithmetic
open Aeneas Aeneas.Std Result WP

theorem shifted_bit_success (index : U64) (level : U8)
    (hlevel : level.val < 64) :
    ∃ shifted : U64, ∃ bit : U64, ∃ out : U32,
      (index >>> level) = .ok shifted ∧
      lift (shifted &&& 1#u64) = .ok bit ∧
      lift (UScalar.cast .U32 bit) = .ok out ∧
      out.val = ((index.val >>> level.val) &&& 1) ∧ out.val ≤ 1 := by
  have hlevel' : level.val < UScalarTy.U64.numBits := by simpa using hlevel
  obtain ⟨shifted, hshift, hshiftValue⟩ :=
    WP.spec_imp_exists (UScalar.ShiftRight_spec index level hlevel')
  let bit := shifted &&& 1#u64
  let out := UScalar.cast .U32 bit
  have hone : (1#u64).val = 1 := by norm_num [UScalar.ofNatCore_val_eq]
  have hbit : bit.val = ((index.val >>> level.val) &&& 1) := by
    dsimp only [bit]
    rw [UScalar.val_and, hshiftValue.1, hone]
  have hbitBound : bit.val ≤ 1 := by
    rw [hbit]
    exact Nat.and_le_right
  have hcast : out.val = bit.val := by
    exact AspisR1.ExtractedMaskReducerOps.narrow_exact bit (by omega)
  refine ⟨shifted, bit, out, hshift, rfl, rfl, ?_, ?_⟩
  · exact hcast.trans hbit
  · omega

theorem one_minus_bit_success (bit : U32) (hbit : bit.val ≤ 1) :
    ∃ out : U32, (1#u32 - bit : Result U32) = .ok out ∧
      out.val = 1 - bit.val ∧ out.val ≤ 1 := by
  have hone : (1#u32).val = 1 := by norm_num [UScalar.ofNatCore_val_eq]
  have hsafe : bit.val ≤ (1#u32).val := by rw [hone]; exact hbit
  obtain ⟨out, hr, hv⟩ :=
    AspisR1.ExtractedMaskReducerOps.sub_success (1#u32) bit hsafe
  refine ⟨out, hr, ?_, ?_⟩
  · simpa only [hone] using hv
  · have hout : out.val = 1 - bit.val := by simpa only [hone] using hv
    rw [hout]
    exact Nat.sub_le _ _

#print axioms shifted_bit_success
#print axioms one_minus_bit_success
end AspisR1.CopyLinkBitArithmetic
