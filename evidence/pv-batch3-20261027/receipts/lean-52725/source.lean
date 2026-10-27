import PV_B3_FieldTransport
namespace PV_B3_FieldScalar
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace N
open PV_B3_Copy_117
abbrev P := aspis_core.field.P
abbrev subP := aspis_core.field.ct.subtract_p
abbrev red := aspis_core.field.ct.reduce64
abbrev add := aspis_core.field.M31.add
abbrev sub := aspis_core.field.M31.sub
abbrev mul := aspis_core.field.M31.mul
abbrev neg := aspis_core.field.M31.neg
abbrev double := aspis_core.field.M31.double
end N
namespace O
open R1Z.ProverRwP7CurrentFieldSource
abbrev P := aspis_core.field.P
abbrev subP := aspis_core.field.ct.subtract_p
abbrev red := aspis_core.field.ct.reduce64
abbrev add := aspis_core.field.M31.add
abbrev sub := aspis_core.field.M31.sub
abbrev mul := aspis_core.field.M31.mul
abbrev neg := aspis_core.field.M31.neg
abbrev double := aspis_core.field.M31.double
end O

theorem p : N.P = O.P := rfl
theorem subtract (x : U32) : N.subP x = O.subP x := rfl
theorem reduce (x : U64) : N.red x = O.red x := rfl
theorem add (a b : U32) : N.add a b = O.add a b := rfl
theorem sub (a b : U32) : N.sub a b = O.sub a b := rfl
theorem mul (a b : U32) : N.mul a b = O.mul a b := rfl
theorem neg (a : U32) : N.neg a = O.neg a := rfl
theorem double (a : U32) : N.double a = O.double a := rfl
#print axioms p
#print axioms subtract
#print axioms reduce
#print axioms add
#print axioms sub
#print axioms mul
#print axioms neg
#print axioms double
end PV_B3_FieldScalar
