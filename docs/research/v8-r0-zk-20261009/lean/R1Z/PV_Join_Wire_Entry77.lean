import R1Z.PV_Join_Wire_Op77
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry77
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op77Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    ∀ {E : Type} (corecloneCloneInst : core.clone.Clone E), (aspis_core.r0.domain.Point E) → Result (aspis_core.r0.domain.Point E) :=
  fun {E} inst p => PV_CB_ShippedOp77.aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone inst p
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op77 _ (PV_Join_Wire_Selection.selected base ops) = @source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext E inst p
  exact R1Z.PV_Join_Wire_Op77.op77_source base ops inst p
#print axioms equation
end R1Z.PV_Join_Wire_Entry77
