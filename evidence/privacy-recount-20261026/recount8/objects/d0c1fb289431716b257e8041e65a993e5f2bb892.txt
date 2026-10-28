import R1Z.PV_CBL_AppendSource
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_AppendBundle
open ProverRwFull
set_option autoImplicit false
abbrev Types (base : ExternalTypes) := PV_CBL_CapacityBundle.Types base
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) :=
  @PV_CBL_AppendSource.selected (Types base) (PV_CBL_CapacityBundle.selected base ops)
theorem op31_source (base : ExternalTypes) (ops : @ExternalFuns (Types base)) (s : String) (t : Str) :
    @ExternalFuns.op31 (Types base) (selected base ops) s t = PV_CBL_StringBytesAdapter.append s t := rfl
theorem op30_source (base : ExternalTypes) (ops : @ExternalFuns (Types base)) (n : Usize) :
    @ExternalFuns.op30 (Types base) (selected base ops) n = PV_CBL_CapacityValue.reference n := rfl
theorem op28_source (base : ExternalTypes) (ops : @ExternalFuns (Types base)) (s : String) :
    @ExternalFuns.op28 (Types base) (selected base ops) s =
      PV_CBL_StringOwnedReference.string_owned_reference s := rfl
theorem op25_source (base : ExternalTypes) (ops : @ExternalFuns (Types base)) (p : String) :
    @ExternalFuns.op25 (Types base) (selected base ops) p =
      PV_CBL_PathOwnedReference.path_owned_reference (PV_CBL_StringViewTypes.base base) p := rfl
theorem op29_source (base : ExternalTypes) (ops : @ExternalFuns (Types base)) (p : String) :
    @ExternalFuns.op29 (Types base) (selected base ops) p =
      PV_CBL_PathOwnedReference.path_owned_reference (PV_CBL_StringViewTypes.base base) p := rfl
theorem op34_source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    @ExternalFuns.op34 (Types base) (selected base ops) T A v = PV_CBL_Op34Reference.empty_reference v := rfl
theorem op35_source (base : ExternalTypes) (ops : @ExternalFuns (Types base)) (T : Type) :
    @ExternalFuns.op35 (Types base) (selected base ops) T = PV_CBL_Op35Reference.default_reference T := rfl
#print axioms op31_source
#print axioms op30_source
#print axioms op28_source
#print axioms op25_source
#print axioms op29_source
#print axioms op34_source
#print axioms op35_source
end R1Z.PV_CBL_AppendBundle
