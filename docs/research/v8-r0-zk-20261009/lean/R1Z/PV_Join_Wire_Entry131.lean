import R1Z.PV_Join_Wire_Op131
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry131
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op131Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    ∀ {T : Type} {Z : Type} (coreconvertAsRefInst : core.convert.AsRef Z T)
      (ZeroizeInst : zeroize.Zeroize Z), (zeroize.Zeroizing Z) → Result T :=
  fun {T Z} view inst x => PV_CB_ShippedOp131.zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref view inst x
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op131 _ (PV_Join_Wire_Selection.selected base ops) = @source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext T Z view inst x
  exact R1Z.PV_Join_Wire_Op131.op131_source base ops view inst x
#print axioms equation
end R1Z.PV_Join_Wire_Entry131
