import R1Z.PV_Join_Wire_Op51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry51
open Aeneas Aeneas.Std Result ProverRwFull PV_CB3_Op51Arbitrary
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    aspis_core.field.wide_exact.WideExact → Result (Array Std.U8 32#usize) :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun x => PV_CB3_Op51Source.Raw.wide_bytes_flat x
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op51 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext x
  exact R1Z.PV_Join_Wire_Op51.op51_source base ops x
#print axioms equation
end R1Z.PV_Join_Wire_Entry51
