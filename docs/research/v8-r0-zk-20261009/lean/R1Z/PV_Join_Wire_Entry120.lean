import R1Z.PV_Join_Wire_Op120
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry120
open Aeneas Aeneas.Std Result  ProverRwFull Aeneas Aeneas.Std Result ProverRwFull PV_CB3_Op120Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    (Array aspis_core.field.QM31 28#usize) → Result aspis_core.field.QM31 :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun p => Raw.boundary_flat p
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op120 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext p
  exact R1Z.PV_Join_Wire_Op120.op120_source base ops p
#print axioms equation
end R1Z.PV_Join_Wire_Entry120
