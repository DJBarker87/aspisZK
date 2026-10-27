import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB3_Op225Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op225
open Aeneas Aeneas.Std Result ProverRwFull PV_CB3_Op225Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op225_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (transfer : Transfer → Raw.Transfer) (withdrawal : Withdrawal → Raw.Withdrawal)
    (p : Public),
    (PV_Join_Wire_Selection.selected base ops).op225 p =
      ProverRwP6TransitionSource.transition (toRaw transfer withdrawal p) := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro transfer withdrawal p
  exact R1Z.PV_CB3_Op225Source.op225_source ops transfer withdrawal p
#print op225_source
#print axioms op225_source
end R1Z.PV_Join_Wire_Op225
