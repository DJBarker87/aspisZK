import R1Z.PV_CBL_CallbackBundle
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_StringCallbackFamily
open ProverRwFull
set_option autoImplicit false
/-- All five supplied reference laws coexist in one additional selection. -/
theorem supplied (b : ExternalTypes) (ops : @ExternalFuns (PV_CBL_CallbackBundle.StringTypes b))
    (s : String) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    (@ExternalFuns.op25 _ (PV_CBL_CallbackBundle.selectedString b ops) s =
      PV_CBL_PathOwnedReference.path_owned_reference (PV_CBL_StringViewTypes.base b) s) ∧
    (@ExternalFuns.op28 _ (PV_CBL_CallbackBundle.selectedString b ops) s =
      PV_CBL_StringOwnedReference.string_owned_reference s) ∧
    (@ExternalFuns.op29 _ (PV_CBL_CallbackBundle.selectedString b ops) s =
      PV_CBL_PathOwnedReference.path_owned_reference (PV_CBL_StringViewTypes.base b) s) ∧
    (@ExternalFuns.op34 _ (PV_CBL_CallbackBundle.selectedString b ops) T A v =
      PV_CBL_Op34Reference.empty_reference v) ∧
    (@ExternalFuns.op35 _ (PV_CBL_CallbackBundle.selectedString b ops) T =
      PV_CBL_Op35Reference.default_reference T) :=
  ⟨PV_CBL_CallbackBundle.op25_source_string b ops s,
   PV_CBL_CallbackBundle.op28_source b ops s,
   PV_CBL_CallbackBundle.op29_source_string b ops s,
   PV_CBL_CallbackBundle.op34_source_string b ops A v,
   PV_CBL_CallbackBundle.op35_source_string b ops T⟩
#print axioms supplied
end R1Z.PV_CBL_StringCallbackFamily
