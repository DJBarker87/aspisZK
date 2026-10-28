import R1Z.ProverRwP6BodyData
import R1Z.PV_CB3_Op225Source
import R1Z.PV_CB3_Op246Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_CB3
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem op225_source (ops : ExternalFuns)
    (transfer : PV_CB3_Op225Source.Transfer → PV_CB3_Op225Source.Raw.Transfer)
    (withdrawal : PV_CB3_Op225Source.Withdrawal → PV_CB3_Op225Source.Raw.Withdrawal)
    (p : PV_CB3_Op225Source.Public) :
    (ProverRwP6BodyStore.selected ops).op225 p =
      ProverRwP6TransitionSource.transition (PV_CB3_Op225Source.toRaw transfer withdrawal p) :=
  PV_CB3_Op225Source.op225_source ops transfer withdrawal p

theorem op246_source (ops : ExternalFuns) {H : Type}
    (inst : aspis_core.digest.Digest32 H) (hash : H) (left right : Array U8 32#usize) :
    (ProverRwP6BodyStore.selected ops).op246 inst hash left right =
      PV_CB3_ShippedOp246.multiproof.binary_parent inst hash left right :=
  PV_CB3_Op246Source.op246_source ops inst hash left right
#print axioms op225_source
#print axioms op246_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_CB3
