import NHU_COMBINED_IMPORT
import NFQ_Reduce
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_RawReduce
/-- The emitted caller uses the exact retained scalar reducer. -/
theorem transport (x : U64) :
 FIq_Native.field.M31.reduce_u62 x=AspisR1SelectedMaskProbe.field.M31.reduce_u62 x := by rfl

theorem result (x : U64) :
 ∃ z, FIq_Native.field.M31.reduce_u62 x=ok z ∧
 z.val=x.val%2147483647 ∧ z.val<2147483647 := by
 rw [transport]
 exact NFQ_Reduce.source x
#print axioms transport
#print axioms result
end AspisR1.NIH_RawReduce
