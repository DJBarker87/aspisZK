import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_TakeSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op3
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_TakeSource
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op3_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ {T : Type}
    (inst : core.default.Default T) (x : T),
    (PV_Join_Wire_Selection.selected base ops).op3 inst x = PV_CB_ShippedTake.core.mem.take inst x := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro T inst x
  exact R1Z.PV_CB_TakeSource.op3_source ops inst x
#print op3_source
#print axioms op3_source
end R1Z.PV_Join_Wire_Op3
