import R1Z.PDict_PureDictionary
import R1Z.PDict_CodecSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_CodecDictionary
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_PureDictionary.native
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_PureDictionary.selected base ops with
    op49 := PDict_CodecSource.aspis_core.field.wide_exact.WideExact.to_limbs
    op50 := PDict_CodecSource.aspis_core.field.wide_exact.WideExact.from_le_bytes }

theorem op49_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op49 = PDict_CodecSource.aspis_core.field.wide_exact.WideExact.to_limbs := rfl

theorem op50_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op50 = PDict_CodecSource.aspis_core.field.wide_exact.WideExact.from_le_bytes := rfl

/-- Serialization has not been assigned an invented iterator interpretation. -/
theorem op51_retained (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op51 = ops.op51 := rfl

#print axioms op49_installed
#print axioms op50_installed
#print axioms op51_retained
end R1Z.PDict_CodecDictionary
