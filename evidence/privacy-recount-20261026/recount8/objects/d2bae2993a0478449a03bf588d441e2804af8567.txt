import R1Z.PV_Join_Wire_Op3
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry3
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_TakeSource
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    ∀ {T : Type} (defaultDefaultInst : core.default.Default T), T → Result (T × T) :=
  fun {T} inst x => PV_CB_ShippedTake.core.mem.take inst x
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op3 _ (PV_Join_Wire_Selection.selected base ops) = @source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext T inst x
  exact R1Z.PV_Join_Wire_Op3.op3_source base ops inst x
#print axioms equation
end R1Z.PV_Join_Wire_Entry3
