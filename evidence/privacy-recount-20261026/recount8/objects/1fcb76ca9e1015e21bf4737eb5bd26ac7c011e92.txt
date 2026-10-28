import R1Z.ProverRwSuccessGeneric
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessBorrow
open Aeneas Aeneas.Std Result ProverRwFull
-- These are value/borrow operations only. Physical destructor association is
-- deliberately not installed by this selector.
def deref {Z : Type} (_ : zeroize.Zeroize Z) (z : zeroize.Zeroizing Z) : Result Z := .ok z
def new {Z : Type} (_ : zeroize.Zeroize Z) (z : Z) : Result (zeroize.Zeroizing Z) := .ok z
def erase {Z : Type} (inst : zeroize.Zeroize Z)
    (z : zeroize.Zeroizing Z) : Result (zeroize.Zeroizing Z) := inst.zeroize z
def asRef {T Z : Type} (inst : core.convert.AsRef Z T) (_ : zeroize.Zeroize Z)
    (z : zeroize.Zeroizing Z) : Result T := inst.as_ref z
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessGeneric.selected ops with
    op127 := deref, op128 := new, op130 := erase, op131 := asRef}

theorem deref_value (ops : ExternalFuns) {Z : Type} (inst : zeroize.Zeroize Z) (z : Z) :
    (selected ops).op127 inst z = .ok z := rfl

theorem new_value (ops : ExternalFuns) {Z : Type} (inst : zeroize.Zeroize Z) (z : Z) :
    (selected ops).op128 inst z = .ok z := rfl

theorem erase_callback (ops : ExternalFuns) {Z : Type} (inst : zeroize.Zeroize Z) (z : Z) :
    (selected ops).op130 inst z = inst.zeroize z := rfl

theorem borrow_callback (ops : ExternalFuns) {T Z : Type}
    (view : core.convert.AsRef Z T) (inst : zeroize.Zeroize Z) (z : Z) :
    (selected ops).op131 view inst z = view.as_ref z := rfl
#print axioms deref_value
#print axioms new_value
#print axioms erase_callback
#print axioms borrow_callback
end R1Z.ProverRwSuccessBorrow
