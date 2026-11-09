import Aeneas
import NNG_verify_finish.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
noncomputable section
namespace NNG_verify_finish.PRVA
@[reducible]
impl_def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 (NNG_call_3 : aspis_core.field.QM31 → aspis_core.field.QM31 → Result Bool) : core.cmp.PartialEq
  aspis_core.field.QM31 aspis_core.field.QM31 := {
  eq := NNG_call_3
  ne := core.cmp.PartialEq.ne.trait_default
    (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 NNG_call_3)
}
set_option pp.explicit false
#print PRVA.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
#print NNG_verify_finish.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
#print core.cmp.PartialEq.ne.trait_default
theorem tA (c) : PRVA.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 c = NNG_verify_finish.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 c := by
  unfold PRVA.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 NNG_verify_finish.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
  rfl
end NNG_verify_finish.PRVA
