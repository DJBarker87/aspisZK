import R1Z.PV_CB_Composition
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_BorrowOutcomes
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem erase_fail (ops : ExternalFuns) {Z : Type} (inst : zeroize.Zeroize Z)
    (x : Z) (e : Error) (h : inst.zeroize x = .fail e) :
    (PV_CB_Composition.selected ops).op130 inst x = .fail e := h
theorem erase_div (ops : ExternalFuns) {Z : Type} (inst : zeroize.Zeroize Z)
    (x : Z) (h : inst.zeroize x = .div) :
    (PV_CB_Composition.selected ops).op130 inst x = .div := h
theorem view_fail (ops : ExternalFuns) {T Z : Type} (view : core.convert.AsRef Z T)
    (inst : zeroize.Zeroize Z) (x : Z) (e : Error) (h : view.as_ref x = .fail e) :
    (PV_CB_Composition.selected ops).op131 view inst x = .fail e := h
theorem view_div (ops : ExternalFuns) {T Z : Type} (view : core.convert.AsRef Z T)
    (inst : zeroize.Zeroize Z) (x : Z) (h : view.as_ref x = .div) :
    (PV_CB_Composition.selected ops).op131 view inst x = .div := h
#print axioms erase_fail
#print axioms erase_div
#print axioms view_fail
#print axioms view_div
end R1Z.PV_CB_BorrowOutcomes
