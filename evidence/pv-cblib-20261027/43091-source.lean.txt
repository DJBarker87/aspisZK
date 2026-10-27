import R1Z.PV_CBL_CallbackBundle
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_StringViewObservation
open ProverRwFull
set_option autoImplicit false
theorem value (base : ExternalTypes) (ops : @ExternalFuns (PV_CBL_CallbackBundle.StringTypes base))
    (s : String) :
    @ExternalFuns.op28 (PV_CBL_CallbackBundle.StringTypes base)
      (PV_CBL_CallbackBundle.selectedString base ops) s = ok s := rfl
/-- Pure value observations; native side-channel/world association remains a separate obligation. -/
theorem observe {A : Type} (f : String→A) (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_CallbackBundle.StringTypes base)) (s : String) :
    (do let p ← @ExternalFuns.op28 (PV_CBL_CallbackBundle.StringTypes base)
            (PV_CBL_CallbackBundle.selectedString base ops) s
        ok (f p)) = ok (f s) := rfl
#print axioms value
#print axioms observe
end R1Z.PV_CBL_StringViewObservation
