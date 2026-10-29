import R1Z.PV_RDCD3_V265Inverse
import R1Z.PV_RDCD3_Result194
import R1Z.PV_RDCD3_Endian194
import R1Z.PV_RDCD3_ArrayWrite194
import R1Z.PV_RDCD3_Cast194
import R1Z.PV_RDCD3_WordAll194
import R1Z.PV_RDCD3_Control194
import R1Z.PV_RDCD3_Index194

namespace R1Z.PV_RDCD3_V265
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_AL_CircleOwned
abbrev Q := aspis_core.field.QM31
abbrev Point := aspis_core.circle.SecureCirclePoint
abbrev Row := aspis_core.r0_transcript.CircleRow

/-- Existing owned control is exactly the deployed Option ok_or match. -/
theorem okOr_binding {T E : Type} (o : Option T) (e : E) :
    PV_AL_CircleControl.okOr o e = PV_RDCD3_Result194.okOr o e := by
  cases o <;> rfl

theorem unwrap_binding {T E : Type} (r : core.result.Result T E) (fallback : E → Result T) :
    PV_AL_CircleControl.unwrapOrElse r fallback =
      PV_RDCD3_Result194.unwrapOrElse r fallback := rfl

/-- Full static source control plus its concrete inverse backend, all inputs.
No Option<fn>, pointer comparison, arbitrary inverse or success premise enters.
Native structural association is recorded separately, with existing tool trust. -/
theorem complete :
    (∀ x, aspis_core.field.M31.inv x = PV_RDCD3_V265Inverse.inverse x) ∧
    (∀ (block : Array U8 32#usize) (row : Row),
      PV_AL_CircleNative.nativeCircle block row = circle_owned block row) :=
  ⟨PV_RDCD3_V265Inverse.source,PV_AL_CircleNative.source_reference⟩

/-- Complete Result carrier projection retains every error and divergence. -/
def project {B : Type} (decode : Point → B) : Result Point → Result B
  | ok point => ok (decode point)
  | fail e => fail e
  | div => div

theorem carrier {B : Type} (decode : Point → B) (block : Array U8 32#usize) (row : Row) :
    project decode (PV_AL_CircleNative.nativeCircle block row) =
      project decode (circle_owned block row) :=
  congrArg (project decode) (PV_AL_CircleNative.source_reference block row)

#print axioms okOr_binding
#print axioms unwrap_binding
#print axioms complete
#print axioms carrier
end R1Z.PV_RDCD3_V265
