import R1Z.PV_Join_Wire_Op72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry72
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op72Transport PV_CB_Op72Exact
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    aspis_core.field.QM31 → (Slice Std.U8) → Result (Slice Std.U8) :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun x bytes => PV_CB_ShippedOp72.aspis_core.field.QM31.write_le_bytes (encode x) bytes
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op72 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext x bytes
  exact R1Z.PV_Join_Wire_Op72.op72_source base ops x bytes
#print axioms equation
end R1Z.PV_Join_Wire_Entry72
