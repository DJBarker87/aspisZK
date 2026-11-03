import NEF_FrozenInvRef.Funs
import NBG_InverseBridge
set_option autoImplicit false
namespace NET_MultiplyBridge
open Aeneas Aeneas.Std Result AspisR1

/-- The independently emitted checked reducer equals the coherent release
reducer on every raw U64. Its folds fit; no concrete large reduction is run. -/
theorem reducer (x : U64) :
 NEF_FrozenInvRef.field.reduce_u64 x = FIo_Native.aspis_core.field.reduce_u64 x := by
 let m := FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)
 have small : m.val < 4294967294 := by
  rw [LPf_ReductionWord.twice_value]
  apply LPe_MersenneReduction.fold_twice_lt
  scalar_tac
 unfold NEF_FrozenInvRef.field.reduce_u64 FIo_Native.aspis_core.field.reduce_u64
 simp only [NEF_FrozenInvRef.field.P,FIo_Native.aspis_core.field.P,lift,bind_tc_ok,
  FIo_ReduceFacts.shr31,FIo_ReduceBounds.checked]
 change (if UScalar.cast .U32 m >= 2147483647#u32
   then UScalar.cast .U32 m - 2147483647#u32 else ok (UScalar.cast .U32 m)) =
  (if UScalar.cast .U32 m >= 2147483647#u32
   then ok (U32.wrapping_sub (UScalar.cast .U32 m) 2147483647#u32) else ok (UScalar.cast .U32 m))
 split
 · apply FIo_ScalarBridge.sub
   scalar_tac
 · rfl

/-- Full raw U32 domain, including the actual checked product and Result. -/
theorem product (x y : U32) :
 NEF_FrozenInvRef.field.M31.mul x y = FIo_Native.aspis_core.field.M31.mul x y := by
 have bound : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val < UScalar.size .U64 := by
  have h := LPf_BaseMultiply.product_bound x y
  have cx : (UScalar.cast .U64 x).val=x.val := by scalar_tac
  have cy : (UScalar.cast .U64 y).val=y.val := by scalar_tac
  simpa only [cx,cy] using h
 have native := FIo_ScalarBridge.mul (UScalar.cast .U64 x) (UScalar.cast .U64 y) bound
 simp only [NEF_FrozenInvRef.field.M31.mul,FIo_Native.aspis_core.field.M31.mul,
  lift,bind_tc_ok,native,reducer]

/-- Paired meaning for each of the four product replies in the adopted CM
seven-call log; the caller must still establish its other child domains. -/
theorem product_reply (x y : U32) : ∃ z,
 NEF_FrozenInvRef.field.M31.mul x y=ok z ∧
 z.val=(x.val*y.val)%2147483647 ∧ z.val<2147483647 := by
 rw [product]
 exact LPf_BaseMultiply.source x y

#print axioms reducer
#print axioms product
#print axioms product_reply
end NET_MultiplyBridge
