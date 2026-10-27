import XRn_Join_Funs
import LPf_ReductionWord
import XSd_DotSequence
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSd_DotReduce
/-- The already pinned checked private reducer equals the current native
wrapping private reducer. Checked additions are discharged by existing bounds. -/
theorem body (x : U64) : XRn_Join_Release.fast_pairing.canonical.reduce x =
 FIo_Native.fast_pairing.canonical.reduce x := by
 unfold XRn_Join_Release.fast_pairing.canonical.reduce FIo_Native.fast_pairing.canonical.reduce
 simp only [XRn_Join_Release.fast_pairing.canonical.P,FIo_Native.fast_pairing.canonical.P,
 lift,bind_tc_ok,AspisR1.FIo_ReduceFacts.shr31]
 have mask : core.convert.num.FromU64U32.from 2147483647#u32=2147483647#u64 := rfl
 rw [mask]
 rw [AspisR1.FIo_ReduceBounds.checked x]
 simp only [bind_tc_ok,AspisR1.FIo_ReduceFacts.shr31]
 rw [AspisR1.FIo_ReduceBounds.checked (AspisR1.FIo_ReduceBounds.fold x)]
 simp only [bind_tc_ok]
 change (if AspisR1.FIo_ReduceBounds.fold (AspisR1.FIo_ReduceBounds.fold x) ≥ 2147483647#u64
 then (do let y ← AspisR1.FIo_ReduceBounds.fold (AspisR1.FIo_ReduceBounds.fold x)-2147483647#u64; ok (UScalar.cast .U32 y))
 else ok (UScalar.cast .U32 (AspisR1.FIo_ReduceBounds.fold (AspisR1.FIo_ReduceBounds.fold x)))) =
 (if AspisR1.FIo_ReduceBounds.fold (AspisR1.FIo_ReduceBounds.fold x) ≥ 2147483647#u64
 then ok (UScalar.cast .U32 (U64.wrapping_sub (AspisR1.FIo_ReduceBounds.fold (AspisR1.FIo_ReduceBounds.fold x)) 2147483647#u64))
 else ok (UScalar.cast .U32 (AspisR1.FIo_ReduceBounds.fold (AspisR1.FIo_ReduceBounds.fold x))))
 split
 · rename_i h
   rw [AspisR1.FIo_ScalarBridge.sub _ 2147483647#u64 (by scalar_tac)]
   rfl
 · rfl

theorem total (x : U64) : ∃ z,
 XRn_Join_Release.fast_pairing.canonical.reduce x=ok z ∧
 z.val=x.val%2147483647 ∧ z.val<2147483647 := by
 rw [body]
 exact AspisR1.LPf_ReductionWord.native_reduce x
#print axioms body
#print axioms total
end XSd_DotReduce
