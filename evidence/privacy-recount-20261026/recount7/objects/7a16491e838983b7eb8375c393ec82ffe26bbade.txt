import R1Z.PV_Join_Wire_Op84
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry84
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op84Exact
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    (Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) → Std.U8 →
        (Slice Std.U8) → Result (Array Std.U8 32#usize) :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun hash tag values => PV_CB_ShippedOp84Fresh.aspis_core.r0.merkle.leaf hash tag values
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op84 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext hash tag values
  exact R1Z.PV_Join_Wire_Op84.op84_source base ops hash tag values
#print axioms equation
end R1Z.PV_Join_Wire_Entry84
