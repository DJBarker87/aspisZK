import Aeneas
import NNG_verify_finish.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
noncomputable section
theorem PRVEq_partialEq_ne_default {Self Rhs : Type} (c : Self → Rhs → Result Bool) :
    ({ eq := c, ne := fun s o => core.cmp.PartialEq.ne.default c s o } : core.cmp.PartialEq Self Rhs) = { eq := c } := by
  have h : (fun s o => core.cmp.PartialEq.ne.default c s o) = core.cmp.PartialEq.ne._default c := by
    funext s o
    simp only [core.cmp.PartialEq.ne.default, core.cmp.PartialEq.ne._default, id]
    congr 1; funext b; cases b <;> rfl
  rw [h]; rfl
#print axioms PRVEq_partialEq_ne_default
namespace NNG_verify_finish.PRVA
@[reducible]
impl_def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 (NNG_call_3 : aspis_core.field.QM31 → aspis_core.field.QM31 → Result Bool) : core.cmp.PartialEq
  aspis_core.field.QM31 aspis_core.field.QM31 := {
  eq := NNG_call_3
  ne := core.cmp.PartialEq.ne.trait_default
    (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 NNG_call_3)
}
theorem tA : @PRVA.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 = @NNG_verify_finish.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 := by
  funext c
  unfold PRVA.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 NNG_verify_finish.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
  exact PRVEq_partialEq_ne_default c
#print axioms tA
end NNG_verify_finish.PRVA
