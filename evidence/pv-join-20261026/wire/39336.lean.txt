import R1Z.PV_Join_Wire_Op109
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry109
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op109Transport PV_CB_Op109Exact
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    aspis_core.field.wide_exact.WideExact → Result (Option
        aspis_core.field.wide_exact.WideExact) :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun x => (do
      let value ← PV_CB_ShippedOp109.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv (encodeW x)
      ok (value.map decodeW))
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op109 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext x
  exact R1Z.PV_Join_Wire_Op109.op109_source base ops x
#print axioms equation
end R1Z.PV_Join_Wire_Entry109
