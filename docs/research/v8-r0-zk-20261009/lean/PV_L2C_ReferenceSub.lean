import PV_L2C_NormalizeSource
set_option autoImplicit false
namespace PV_L2C_ReferenceSub
open Aeneas Aeneas.Std Result AspisR1ProverBalance9 PV_L2C_ReferenceArithmetic
open PV_L2C_NormalizeSource

theorem m31_sub (x y : U32) :
    aspis_core.field.M31.sub x y=ok (wrap (PV_L2C_M31.sub x.bv y.bv)) := by
  calc
    _ = normalize (U32.wrapping_sub (U32.wrapping_add x aspis_core.field.P) y) := sub_cut x y
    _ = ok (wrap (PV_L2C_M31.subtractP
        (U32.wrapping_sub (U32.wrapping_add x aspis_core.field.P) y).bv)) := normalize_native _
    _ = _ := congrArg (fun w => ok (wrap (PV_L2C_M31.subtractP w))) (sub_input x y)
#print axioms m31_sub
end PV_L2C_ReferenceSub
