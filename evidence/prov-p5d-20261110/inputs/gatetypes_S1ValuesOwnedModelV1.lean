import CurrentCompactCallerTypesV1
set_option autoImplicit false
namespace AspisS1ValuesOwned
/-- Full native codec carrier: every error variant, with no projection. -/
abbrev CodecError := AspisR1CurrentCaller.compact.CodecError
#print axioms CodecError
end AspisS1ValuesOwned
