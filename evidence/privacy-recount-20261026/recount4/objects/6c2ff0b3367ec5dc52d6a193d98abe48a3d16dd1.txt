import R1Z.PV_Join_Wire_Op71
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry71
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op71Transport PV_CB_Op71Exact
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    (Slice Std.U8) → Result (Option aspis_core.field.QM31) :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun bytes => (do
      let value ← PV_CB_ShippedOp71.aspis_core.field.QM31.from_le_bytes bytes
      ok (value.map decode))
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op71 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext bytes
  exact R1Z.PV_Join_Wire_Op71.op71_source base ops bytes
#print axioms equation
end R1Z.PV_Join_Wire_Entry71
