import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op77Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op77
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op77Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op77_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ {E : Type} (inst : core.clone.Clone E)
    (p : aspis_core.r0.domain.Point E),
    (PV_Join_Wire_Selection.selected base ops).op77 inst p =
      PV_CB_ShippedOp77.aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone inst p := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro E inst p
  exact R1Z.PV_CB_Op77Source.op77_source ops inst p
#print op77_source
#print axioms op77_source
end R1Z.PV_Join_Wire_Op77
