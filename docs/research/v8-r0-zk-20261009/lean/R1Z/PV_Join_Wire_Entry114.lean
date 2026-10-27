import R1Z.PV_Join_Wire_Op114
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry114
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op114Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    aspis_core.state_only_hiding.StateOnlyHidingContext →
        aspis_core.state_only_hiding.StateOnlyHidingContext → Result Bool :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun a b => PV_CB_ShippedOp114.aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq a b
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op114 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext a b
  exact R1Z.PV_Join_Wire_Op114.op114_source base ops a b
#print axioms equation
end R1Z.PV_Join_Wire_Entry114
