import R1Z.PV_RW_CompressReference
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressEmission
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
/-- [pv_rw_step::generated::shipped_step]:
    Source: 'generated.rs', lines 13:0-17:1
    Visibility: public -/
def generated.shipped_step
  (compressed : aspis_core.field.QM31) (power : aspis_core.field.QM31)
  (value : aspis_core.field.M31) (lambda : aspis_core.field.QM31) :
  Result (aspis_core.field.QM31 × aspis_core.field.QM31)
  := do
  let q ← aspis_core.field.QM31.mul_m31 power value
  let compressed1 ← aspis_core.field.QM31.add compressed q
  let power1 ← aspis_core.field.QM31.mul power lambda
  ok (compressed1, power1)

theorem emitted_step (out power : aspis_core.field.QM31)
    (value : aspis_core.field.M31) (lambda : aspis_core.field.QM31) :
    generated.shipped_step out power value lambda =
      PV_RW_CompressStep.shipped lambda value (out,power) := rfl

theorem emitted_fold (lambda : aspis_core.field.QM31)
    (values : List aspis_core.field.M31) (state : aspis_core.field.QM31 × aspis_core.field.QM31) :
    PV_RW_CompressStep.run (fun value state =>
      generated.shipped_step state.1 state.2 value lambda) values state =
      PV_CompressList.stateFold values lambda state := by
  change PV_RW_CompressStep.run (PV_RW_CompressStep.shipped lambda) values state = _
  exact PV_RW_CompressStep.shipped_fold lambda values state
#print axioms emitted_step
#print axioms emitted_fold
end R1Z.PV_RW_CompressEmission
