import Aeneas
import NNG_verify_finish.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
noncomputable section
namespace NNG_verify_finish.PRVA
variable (NNG_call_3 : aspis_core.field.QM31 → aspis_core.field.QM31 → Result Bool)

@[reducible]
impl_def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 : core.cmp.PartialEq
  aspis_core.field.QM31 aspis_core.field.QM31 := {
  eq := NNG_call_3
  ne := core.cmp.PartialEq.ne.trait_default
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
}
theorem tA : @PRVA.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 = @NNG_verify_finish.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 := by rfl
end NNG_verify_finish.PRVA
namespace PRVB
open NNG_verify_finish
variable (NNG_call_3 : aspis_core.field.QM31 → aspis_core.field.QM31 → Result Bool)
impl_def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 : core.cmp.PartialEq
  aspis_core.field.QM31 aspis_core.field.QM31 := {
  eq := NNG_call_3
  ne := core.cmp.PartialEq.ne.trait_default
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
}
end PRVB
