import R1Z.PV_RunJoin_OsFailurePure
import R1Z.PDict_CodecDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_VariantIdentity
open ProverRwFull

theorem selected_variant (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base)) :
    @PV_RunJoin_OsFailurePure.VariantIdentity (PDict_CodecDictionary.native base)
      (PDict_CodecDictionary.selected base ops) := by
  change (PDict_CodecDictionary.selected base ops).op233 = ProverRwCallerBinding.variantEq
  funext a b
  cases a <;> cases b <;> rfl

#print axioms selected_variant
end R1Z.PV_RunJoin_VariantIdentity
