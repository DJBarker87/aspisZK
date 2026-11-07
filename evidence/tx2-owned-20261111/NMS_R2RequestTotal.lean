import NMS_R2RequestSplitTotal
set_option autoImplicit false
namespace NMS_R2RequestTotal
open Aeneas Aeneas.Std Result WP
/-- The Option-shaped canonical decoder needs no outer fail/div at its
native source occurrence. This proof concerns arbitrary symbolic input,
including every rejected request; no honest fixture is used. -/
@[step] theorem decode_spec (bytes : Slice U8) :
 AspisR1.NFY_JHd_RequestNative.decode bytes ⦃ _ => True ⦄ := by
 unfold AspisR1.NFY_JHd_RequestNative.decode
 step*

theorem total (bytes : Slice U8) :
 ∃ reply, AspisR1.NFY_JHd_RequestNative.decode bytes = ok reply := by
 obtain ⟨reply,run,_⟩ := spec_imp_exists (decode_spec bytes)
 exact ⟨reply,run⟩
#print axioms decode_spec
#print axioms total
end NMS_R2RequestTotal
