import NDO_JGj_RawBounds
set_option autoImplicit false
namespace AspisR1.JGj_ScalarNotation
open Aeneas Aeneas.Std Result FIq_Native
theorem add (x y : U64) : (x+y : Result U64)=UScalar.add x y := by rfl
theorem sub (x y : U64) : (x-y : Result U64)=UScalar.sub x y := by rfl
theorem wide (x : U32) : core.convert.num.FromU64U32.from x=FJb_WideSum4.wide x := by rfl
#print axioms add
#print axioms sub
#print axioms wide
end AspisR1.JGj_ScalarNotation
