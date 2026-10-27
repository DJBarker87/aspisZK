import R1Z.PV_Join_Wire_Op127
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry127
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op127Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z), (zeroize.Zeroizing Z) → Result Z :=
  fun {Z} inst x => PV_CB_ShippedOp127.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst x
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op127 _ (PV_Join_Wire_Selection.selected base ops) = @source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext Z inst x
  exact R1Z.PV_Join_Wire_Op127.op127_source base ops inst x
#print axioms equation
end R1Z.PV_Join_Wire_Entry127
