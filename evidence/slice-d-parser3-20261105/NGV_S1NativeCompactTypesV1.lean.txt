import CurrentCompactCallerTypesV1
set_option autoImplicit false
namespace AspisS1NativeCompact
/-- Complete native codec-error carrier, shared with its actual caller. -/
abbrev compact.CodecError := AspisR1CurrentCaller.compact.CodecError
#print axioms AspisS1NativeCompact.compact.CodecError
end AspisS1NativeCompact
