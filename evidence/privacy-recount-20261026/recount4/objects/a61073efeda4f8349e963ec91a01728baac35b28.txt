import R1Z.PV_Join_Wire_Op118
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry118
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op118Transport PV_CB_Op118Exact
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    (Array aspis_core.field.QM31 10#usize) → Result (Array (Array
        aspis_core.field.QM31 10#usize) 3#usize) :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun x => (do
      let value ← PV_CB_ShippedOp118.aspis_core.state_only_prefix.r0.statement_points (encodeArray x)
      ok (decodePoints value))
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op118 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext x
  exact R1Z.PV_Join_Wire_Op118.op118_source base ops x
#print axioms equation
end R1Z.PV_Join_Wire_Entry118
