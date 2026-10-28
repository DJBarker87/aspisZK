import R1Z.PV_CB_State
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Borrow
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Only source value/callback laws. Native zeroization/Drop and side channels
are not inferred from these equations. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_State.selected ops with
    op127 := ProverRwSuccessBorrow.deref
    op128 := ProverRwSuccessBorrow.new
    op130 := ProverRwSuccessBorrow.erase
    op131 := ProverRwSuccessBorrow.asRef}
theorem op127_installed (ops : ExternalFuns) {Z : Type} (inst : zeroize.Zeroize Z) (x : Z) :
    (selected ops).op127 inst x = .ok x := rfl
theorem op128_installed (ops : ExternalFuns) {Z : Type} (inst : zeroize.Zeroize Z) (x : Z) :
    (selected ops).op128 inst x = .ok x := rfl
theorem op130_installed (ops : ExternalFuns) {Z : Type} (inst : zeroize.Zeroize Z) (x : Z) :
    (selected ops).op130 inst x = inst.zeroize x := rfl
theorem op131_installed (ops : ExternalFuns) {T Z : Type}
    (view : core.convert.AsRef Z T) (inst : zeroize.Zeroize Z) (x : Z) :
    (selected ops).op131 view inst x = view.as_ref x := rfl
#print axioms op127_installed
#print axioms op128_installed
#print axioms op130_installed
#print axioms op131_installed
end R1Z.PV_CB_Borrow
