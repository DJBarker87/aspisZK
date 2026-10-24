import CurrentCompactFirstCompositionV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.verifier
/-- The full retained caller phase carrier, with every variant and payload.
This naming alias supplies the nominal phase absent from the selected legacy
public-preparation cache. Source-body transports below use release None. -/
abbrev Phase := AspisR1PublicPreparation.FirstCaller.Phase
end AspisR1PublicPreparation.verifier

#print axioms AspisR1PublicPreparation.verifier.Phase
