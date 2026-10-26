import R1Z.PV_CB_Take
import R1Z.PV_CB_TakeRef
set_option autoImplicit false
namespace R1Z.PV_CB_TakeExtraction
open Aeneas Aeneas.Std Result ProverRwFull
/-- Universal extracted reference equality; the native gates cover only their
named monomorphizations. No arbitrary native Default/Drop law is inferred. -/
theorem reference_eq {T : Type} (inst : core.default.Default T) (x : T) :
    PV_CB_TakeRef.reference.take inst x = ProverRwSuccessGeneric.take inst x := rfl
noncomputable section
variable [ExternalTypes]
theorem installed_reference (ops : ExternalFuns) {T : Type}
    (inst : core.default.Default T) (x : T) :
    (PV_CB_Take.selected ops).op3 inst x = PV_CB_TakeRef.reference.take inst x := rfl
theorem fail_preserved {T : Type} (inst : core.default.Default T) (x : T)
    (e : Error) (h : inst.default = .fail e) :
    PV_CB_TakeRef.reference.take inst x = .fail e := by
  unfold PV_CB_TakeRef.reference.take
  rw [h]
  rfl
theorem div_preserved {T : Type} (inst : core.default.Default T) (x : T)
    (h : inst.default = .div) :
    PV_CB_TakeRef.reference.take inst x = .div := by
  unfold PV_CB_TakeRef.reference.take
  rw [h]
  rfl
#print axioms reference_eq
#print axioms installed_reference
#print axioms fail_preserved
#print axioms div_preserved
end
end R1Z.PV_CB_TakeExtraction
