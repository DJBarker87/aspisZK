import AspisR1ProverBalance9.Funs
set_option autoImplicit false
namespace PV_L2C_SubPrimitive
open Aeneas Aeneas.Std Result
#print U32.wrapping_sub
#print UScalar.wrapping_sub
#print U32.wrapping_add
#print UScalar.wrapping_add

theorem wrapped_sub (x y : U32) :
    U32.wrapping_sub x y=(⟨x.bv-y.bv⟩ : U32) := by rfl
#print axioms wrapped_sub

theorem wrapped_add (x y : U32) :
    U32.wrapping_add x y=(⟨x.bv+y.bv⟩ : U32) := by rfl
#print axioms wrapped_add
end PV_L2C_SubPrimitive
