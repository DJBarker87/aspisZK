import S9ShiftCountCompatV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisR1S9S3U16ShiftCompatV1

/-- The actual inner16 loop bound makes the current wrapping-count shim agree
with the checked scalar shift used by the existing S3 mask-bit theorem. This
proves the checked event rather than assuming its success. -/
theorem checked_u16_shl_compat (x : U16) (bit : Usize) (hbit : bit.val < 16) :
    (x <<< bit : Result U16)=.ok (AspisR1S9ShiftCountCompatV1.u16Shl x bit) := by
  have hs := UScalar.ShiftLeft_spec x bit (UScalar.size UScalarTy.U16)
    (by
      change bit.val < UScalarTy.U16.numBits
      simpa only [UScalarTy.U16_numBits_eq] using hbit)
    rfl
  obtain ⟨shifted,hrun,hvalue⟩ := WP.spec_imp_exists hs
  have hbits := AspisR1S9ShiftCountCompatV1.u16Shl_bv x bit
  rw [Nat.mod_eq_of_lt hbit] at hbits
  have hval : (AspisR1S9ShiftCountCompatV1.u16Shl x bit).val=
      (x.val <<< bit.val) % 2^16 := by
    calc
      (AspisR1S9ShiftCountCompatV1.u16Shl x bit).val =
          (AspisR1S9ShiftCountCompatV1.u16Shl x bit).bv.toNat :=
        (UScalar.bv_toNat _).symm
      _ = (x.bv.shiftLeft bit.val).toNat := congrArg BitVec.toNat hbits
      _ = (x.bv.toNat <<< bit.val) % 2^16 := by
        simpa only [BitVec.shiftLeft_eq,UScalarTy.U16_numBits_eq] using
          (BitVec.toNat_shiftLeft (x:=x.bv) (n:=bit.val))
      _ = (x.val <<< bit.val) % 2^16 := by rw [UScalar.bv_toNat]
  have hsize : UScalar.size UScalarTy.U16=2^16 := by
    rw [UScalar.size_UScalarTyU16,U16.size,U16.numBits,UScalarTy.U16_numBits_eq]
  have he : shifted=AspisR1S9ShiftCountCompatV1.u16Shl x bit := by
    apply UScalar.eq_of_val_eq
    calc
      shifted.val = (x.val <<< bit.val) % UScalar.size UScalarTy.U16 := hvalue.1
      _ = (x.val <<< bit.val) % 2^16 := by rw [hsize]
      _ = (AspisR1S9ShiftCountCompatV1.u16Shl x bit).val := hval.symm
  rw [he] at hrun
  exact hrun

#print axioms checked_u16_shl_compat
end AspisR1S9S3U16ShiftCompatV1
