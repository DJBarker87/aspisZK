import R1Z.PV_CBL_CallbackBundle
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_SelectionAudit
open ProverRwFull
set_option autoImplicit false

theorem idempotent [ExternalTypes] (ops : ExternalFuns) :
    PV_CBL_CallbackBundle.selected (PV_CBL_CallbackBundle.selected ops) =
      PV_CBL_CallbackBundle.selected ops := rfl

theorem all_idempotent (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_CallbackBundle.Types base)) :
    PV_CBL_CallbackBundle.selectedAll base (PV_CBL_CallbackBundle.selectedAll base ops) =
      PV_CBL_CallbackBundle.selectedAll base ops := rfl
#print axioms idempotent
#print axioms all_idempotent
end R1Z.PV_CBL_SelectionAudit
