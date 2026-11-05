import NHI_ScalarStep
set_option autoImplicit false
namespace NHI_GroupDispatch
open Aeneas Aeneas.Std Result

/-- Only the S2/2048-byte caller domain selects this branch. The fallback
remains part of grouped_inactive_pair outside this explicitly stated domain. -/
theorem source (w : FIo_Native.weights.Weights) (bytes : Slice U8)
 (low : Array FIo_Native.aspis_core.field.wide_exact.WideExact 16#usize)
 (s2 : w.variant=FIo_Native.transport.Variant.S2) (size : bytes.val.length=2048) :
 FIo_Native.weights.grouped_inactive_pair w bytes low=
 FIo_Native.weights.s2_grouped_inactive_pair bytes low := by
 have cap : 4096<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 have product : Usize.wrapping_mul 64#usize 32#usize=2048#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_mul_val_eq]
  change (64*32)%UScalar.size .Usize=2048
  exact Nat.mod_eq_of_lt (by omega)
 have message : Slice.len bytes=2048#usize := by
  apply UScalar.eq_of_val_eq
  rw [Slice.len_val]
  change bytes.val.length=(2048#usize).val
  rw [size] <;> rfl
 simp only [FIo_Native.weights.grouped_inactive_pair,s2,
  FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
  FIo_Native.transport.Variant.read_discriminant,bind_tc_ok]
 simp only [product,message,lift,bind_tc_ok]
 rfl

#print axioms source
end NHI_GroupDispatch
