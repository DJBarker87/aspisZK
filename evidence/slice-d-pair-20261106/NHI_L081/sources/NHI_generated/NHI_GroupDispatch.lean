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
 simp only [FIo_Native.weights.grouped_inactive_pair,s2,
  FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
  FIo_Native.transport.Variant.read_discriminant,bind_tc_ok]
 simp [Slice.len_val,Slice.length,size]

#print axioms source
end NHI_GroupDispatch
