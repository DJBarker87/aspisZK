import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD_Cast194
open Aeneas Aeneas.Std
/--1.94.1 impl_from! body, small as Self, at the retained scalar-cast boundary. -/
def from32to64 (small : U32) : U64 := UScalar.cast .U64 small
theorem binding (small : U32) : from32to64 small = core.convert.num.FromU64U32.from small := rfl
/-- The bool instantiation of the same1.94.1 macro retains exact0/1 values. -/
theorem bool_false : UScalar.cast_fromBool .U32 false = 0#u32 := rfl
theorem bool_true : UScalar.cast_fromBool .U32 true = 1#u32 := rfl
#print axioms binding
#print axioms bool_false
#print axioms bool_true
#print UScalar.cast
end R1Z.PV_RDCD_Cast194
