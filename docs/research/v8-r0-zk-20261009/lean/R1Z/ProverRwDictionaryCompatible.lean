import R1Z.ProverRwDictionaryDomain
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryCompatible
open ProverRwFull
variable [ExternalTypes]

/-- The final selector retains every installed scalar entry. Existing
operation/model theorems may therefore be instantiated at this selector. -/
theorem scalar_retraction (ops : ExternalFuns) :
    ProverRwDictionaryScalar.selected (ProverRwDictionaryDomain.selected ops) =
      ProverRwDictionaryDomain.selected ops := by rfl

/-- The actual caller's earlier context/layout/sampler installation is also
retained, without an additional dictionary equation premise. -/
theorem caller_retraction (ops : ExternalFuns) :
    ProverRwOuterMapErr.selected (ProverRwDictionaryDomain.selected ops) =
      ProverRwDictionaryDomain.selected ops := by rfl

#print axioms scalar_retraction
#print axioms caller_retraction
end R1Z.ProverRwDictionaryCompatible
