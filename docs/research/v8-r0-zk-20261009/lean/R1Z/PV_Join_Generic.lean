import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_TakeSource
import R1Z.PV_CB_Op77Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Generic
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev selected := ProverRwP6BodyStore.selected
theorem op3_source (ops : ExternalFuns) {T : Type}
    (inst : core.default.Default T) (x : T) :
    (selected ops).op3 inst x = PV_CB_ShippedTake.core.mem.take inst x := by
  exact PV_CB_TakeSource.op3_source ops inst x
#print axioms op3_source
theorem op77_source (ops : ExternalFuns) {E : Type} (inst : core.clone.Clone E)
    (p : aspis_core.r0.domain.Point E) :
    (selected ops).op77 inst p =
      PV_CB_ShippedOp77.aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone inst p := by
  exact PV_CB_Op77Source.op77_source ops inst p
#print axioms op77_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_Generic
