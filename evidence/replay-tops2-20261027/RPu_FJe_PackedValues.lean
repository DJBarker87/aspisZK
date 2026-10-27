import RPu_FJe_ExternalPackedValue
import RPu_FJe_LeadingPackedValue
import RPu_FJe_FullPackedValue
set_option autoImplicit false
namespace AspisR1.FJe_PackedValues
/-- Complete original native external-packed VALUE,with the same operands. -/
abbrev external := FJe_ExternalPackedValue.value
/-- Complete original native leading-packed VALUE,with the same openings. -/
abbrev leading := FJe_LeadingPackedValue.value
/-- Complete original native interpolated-full-packed VALUE,same state/local. -/
abbrev full := FJe_FullPackedValue.value
#print axioms external
#print axioms leading
#print axioms full
end AspisR1.FJe_PackedValues
