import XRn_Join_Funs
import LPf_CoreReduction
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRx_ValueScalar
/-- The selected source arithmetic has exactly the frozen core reducer body.
This is the scalar needed by A6, not an A3 field-product claim. -/
theorem body (x : U64) :
 aspis_core.field.M31.reduce_u64 x =
 FIo_Native.aspis_core.field.reduce_u64 x := by
 unfold aspis_core.field.M31.reduce_u64 XRn_Join_Field.field.M31.reduce_u64
 change (do let y ← XRn_Join_Field.field.reduce_u64 x; ok y) = _
 have same : XRn_Join_Field.field.reduce_u64 x=FIo_Native.aspis_core.field.reduce_u64 x := by
  unfold XRn_Join_Field.field.reduce_u64 FIo_Native.aspis_core.field.reduce_u64
  simp only [XRn_Join_Field.field.P,FIo_Native.aspis_core.field.P]
 rw [same]
 cases FIo_Native.aspis_core.field.reduce_u64 x <;> rfl

theorem source (x : U64) : ∃ z,
 aspis_core.field.M31.reduce_u64 x=ok z ∧
 z.val=x.val%2147483647 ∧ z.val<2147483647 := by
 rw [body]
 exact AspisR1.LPf_CoreReduction.source x
#print axioms body
#print axioms source
end XRx_ValueScalar
