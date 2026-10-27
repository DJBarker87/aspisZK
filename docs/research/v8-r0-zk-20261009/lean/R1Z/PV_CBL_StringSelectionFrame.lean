import R1Z.PV_CBL_CallbackBundle
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_StringSelectionFrame
open ProverRwFull
set_option autoImplicit false
theorem op25 (b : ExternalTypes) (ops : @ExternalFuns (PV_CBL_CallbackBundle.StringTypes b))
    (s : String) :
    @ExternalFuns.op25 (PV_CBL_CallbackBundle.StringTypes b)
      (PV_CBL_CallbackBundle.selectedString b ops) s =
      PV_CBL_PathOwnedReference.path_owned_reference (PV_CBL_StringViewTypes.base b) s := rfl
theorem op29 (b : ExternalTypes) (ops : @ExternalFuns (PV_CBL_CallbackBundle.StringTypes b))
    (s : String) :
    @ExternalFuns.op29 (PV_CBL_CallbackBundle.StringTypes b)
      (PV_CBL_CallbackBundle.selectedString b ops) s =
      PV_CBL_PathOwnedReference.path_owned_reference (PV_CBL_StringViewTypes.base b) s := rfl
theorem op34 (b : ExternalTypes) (ops : @ExternalFuns (PV_CBL_CallbackBundle.StringTypes b))
    {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    @ExternalFuns.op34 (PV_CBL_CallbackBundle.StringTypes b)
      (PV_CBL_CallbackBundle.selectedString b ops) T A v = PV_CBL_Op34Reference.empty_reference v := rfl
theorem op35 (b : ExternalTypes) (ops : @ExternalFuns (PV_CBL_CallbackBundle.StringTypes b)) (T : Type) :
    @ExternalFuns.op35 (PV_CBL_CallbackBundle.StringTypes b)
      (PV_CBL_CallbackBundle.selectedString b ops) T = PV_CBL_Op35Reference.default_reference T := rfl
#print axioms op25
#print axioms op29
#print axioms op34
#print axioms op35
end R1Z.PV_CBL_StringSelectionFrame
