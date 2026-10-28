import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op114Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op114
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op114Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op114_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (a b : aspis_core.state_only_hiding.StateOnlyHidingContext),
    (PV_Join_Wire_Selection.selected base ops).op114 a b =
      PV_CB_ShippedOp114.aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq a b := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro a b
  exact R1Z.PV_CB_Op114Source.op114_source ops a b
#print op114_source
#print axioms op114_source
end R1Z.PV_Join_Wire_Op114
