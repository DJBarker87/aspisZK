import R1Z.PV_CBL_StringCallbackFamily
import R1Z.PV_CBL_CallbackBundle
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_CallbackAudit
open ProverRwFull
set_option autoImplicit false

theorem supplied_family (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_CallbackBundle.Types base))
    (p : @std.path.PathBuf base) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    (@ExternalFuns.op25 _ (PV_CBL_CallbackBundle.selectedAll base ops) p =
      PV_CBL_PathOwnedReference.path_owned_reference base p) ∧
    (@ExternalFuns.op29 _ (PV_CBL_CallbackBundle.selectedAll base ops) p =
      PV_CBL_PathOwnedReference.path_owned_reference base p) ∧
    (@ExternalFuns.op34 _ (PV_CBL_CallbackBundle.selectedAll base ops) T A v =
      PV_CBL_Op34Reference.empty_reference v) ∧
    (@ExternalFuns.op35 _ (PV_CBL_CallbackBundle.selectedAll base ops) T =
      PV_CBL_Op35Reference.default_reference T) :=
  ⟨PV_CBL_CallbackBundle.op25_source base ops p,
   PV_CBL_CallbackBundle.op29_source base ops p,
   PV_CBL_CallbackBundle.op34_source_all base ops A v,
   PV_CBL_CallbackBundle.op35_source_all base ops T⟩

#print axioms supplied_family
#print axioms PV_CBL_CallbackBundle.op25_source
#print axioms PV_CBL_CallbackBundle.op29_source
#print axioms PV_CBL_CallbackBundle.op34_source_all
#print axioms PV_CBL_CallbackBundle.op35_source_all
#print axioms PV_CBL_CallbackBundle.op28_source
#print axioms PV_CBL_CallbackBundle.op28_source_all
#print axioms PV_CBL_CallbackBundle.op25_source_string
#print axioms PV_CBL_CallbackBundle.op29_source_string
#print axioms PV_CBL_CallbackBundle.op34_source_string
#print axioms PV_CBL_CallbackBundle.op35_source_string
#print axioms PV_CBL_StringCallbackFamily.supplied
end R1Z.PV_CBL_CallbackAudit
