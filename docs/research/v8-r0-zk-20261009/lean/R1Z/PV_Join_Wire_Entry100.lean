import R1Z.PV_Join_Wire_Op100
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry100
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op100Transport PV_CB_Op100Exact
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    aspis_core.field.wide_exact.WideExact → Result
        aspis_core.field.wide_exact.WideExact :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun x => (do
      let y ← PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg (encodeW x)
      ok (decodeW y))
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op100 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext x
  exact R1Z.PV_Join_Wire_Op100.op100_source base ops x
#print axioms equation
end R1Z.PV_Join_Wire_Entry100
