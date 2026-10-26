import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Op127Source
import R1Z.PV_CB_Op128Source
import R1Z.PV_CB_Op130Source
import R1Z.PV_CB_Op131Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Borrow
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev selected := ProverRwP6BodyStore.selected
theorem op127_source (ops : ExternalFuns) {Z : Type} (inst : zeroize.Zeroize Z) (x : Z) :
    (selected ops).op127 inst x =
      PV_CB_ShippedOp127.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst x := by
  exact PV_CB_Op127Source.op127_source ops inst x
#print axioms op127_source
theorem op128_source (ops : ExternalFuns) {Z : Type} (inst : zeroize.Zeroize Z) (x : Z) :
    (selected ops).op128 inst x =
      PV_CB_ShippedOp128.zeroize.Zeroizing.new inst x := by
  exact PV_CB_Op128Source.op128_source ops inst x
#print axioms op128_source
theorem op130_source (ops : ExternalFuns) {Z : Type} (inst : zeroize.Zeroize Z) (x : Z) :
    (selected ops).op130 inst x =
      PV_CB_ShippedOp130.zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize inst x := by
  exact PV_CB_Op130Source.op130_source ops inst x
#print axioms op130_source
theorem op131_source (ops : ExternalFuns) {T Z : Type}
    (view : core.convert.AsRef Z T) (inst : zeroize.Zeroize Z) (x : Z) :
    (selected ops).op131 view inst x =
      PV_CB_ShippedOp131.zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref view inst x := by
  exact PV_CB_Op131Source.op131_source ops view inst x
#print axioms op131_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_Borrow
