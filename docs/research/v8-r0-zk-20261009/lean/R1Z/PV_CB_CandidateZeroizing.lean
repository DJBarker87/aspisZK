import R1Z.PV_CB_CandidateDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CandidateDictionary
open Aeneas Aeneas.Std Result ProverRwFull
theorem op127 (base : ExternalTypes) (ops : @ExternalFuns (native base)) {Z : Type} (inst : zeroize.Zeroize Z) (x : Z) :
    (selected base ops).op127 inst x =
      PV_CB_ShippedOp127.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst x := by
  letI : ExternalTypes := native base
  change (PV_CB_Borrow.selected ops).op127 inst x = _
  exact R1Z.PV_CB_Op127Source.op127_source ops inst x
#print axioms op127
theorem op128 (base : ExternalTypes) (ops : @ExternalFuns (native base)) {Z : Type} (inst : zeroize.Zeroize Z) (x : Z) :
    (selected base ops).op128 inst x =
      PV_CB_ShippedOp128.zeroize.Zeroizing.new inst x := by
  letI : ExternalTypes := native base
  change (PV_CB_Borrow.selected ops).op128 inst x = _
  exact R1Z.PV_CB_Op128Source.op128_source ops inst x
#print axioms op128
theorem op130 (base : ExternalTypes) (ops : @ExternalFuns (native base)) {Z : Type} (inst : zeroize.Zeroize Z) (x : Z) :
    (selected base ops).op130 inst x =
      PV_CB_ShippedOp130.zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize inst x := by
  letI : ExternalTypes := native base
  change (PV_CB_Borrow.selected ops).op130 inst x = _
  exact R1Z.PV_CB_Op130Source.op130_source ops inst x
#print axioms op130
theorem op131 (base : ExternalTypes) (ops : @ExternalFuns (native base)) {T Z : Type}
    (view : core.convert.AsRef Z T) (inst : zeroize.Zeroize Z) (x : Z) :
    (selected base ops).op131 view inst x =
      PV_CB_ShippedOp131.zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref view inst x := by
  letI : ExternalTypes := native base
  change (PV_CB_Borrow.selected ops).op131 view inst x = _
  exact R1Z.PV_CB_Op131Source.op131_source ops view inst x
#print axioms op131
end R1Z.PV_CB_CandidateDictionary
