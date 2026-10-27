import R1Z.PV_CBL_Resume9CallbackAudit
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_Resume9SelectionAudit
open ProverRwFull
set_option autoImplicit false
/-- All seven prior laws coexist with the new join callback, on one dictionary. -/
theorem preserved (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_CallbackBundle.AppendTypes base))
    (p s : String) (tail : Str) (n : Usize) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    @ExternalFuns.op25 (PV_CBL_CallbackBundle.AppendTypes base)
      (PV_CBL_CallbackBundle.selectedJoin base ops) p =
        PV_CBL_PathOwnedReference.path_owned_reference (PV_CBL_StringViewTypes.base base) p ∧
    @ExternalFuns.op28 (PV_CBL_CallbackBundle.AppendTypes base)
      (PV_CBL_CallbackBundle.selectedJoin base ops) s = PV_CBL_StringOwnedReference.string_owned_reference s ∧
    @ExternalFuns.op29 (PV_CBL_CallbackBundle.AppendTypes base)
      (PV_CBL_CallbackBundle.selectedJoin base ops) p =
        PV_CBL_PathOwnedReference.path_owned_reference (PV_CBL_StringViewTypes.base base) p ∧
    @ExternalFuns.op30 (PV_CBL_CallbackBundle.AppendTypes base)
      (PV_CBL_CallbackBundle.selectedJoin base ops) n = PV_CBL_CapacityValue.reference n ∧
    @ExternalFuns.op31 (PV_CBL_CallbackBundle.AppendTypes base)
      (PV_CBL_CallbackBundle.selectedJoin base ops) s tail = PV_CBL_StringBytesAdapter.append s tail ∧
    @ExternalFuns.op34 (PV_CBL_CallbackBundle.AppendTypes base)
      (PV_CBL_CallbackBundle.selectedJoin base ops) T A v = PV_CBL_Op34Reference.empty_reference v ∧
    @ExternalFuns.op35 (PV_CBL_CallbackBundle.AppendTypes base)
      (PV_CBL_CallbackBundle.selectedJoin base ops) T = PV_CBL_Op35Reference.default_reference T := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms preserved
#print axioms R1Z.PV_CBL_CallbackBundle.op26_source
end R1Z.PV_CBL_Resume9SelectionAudit
