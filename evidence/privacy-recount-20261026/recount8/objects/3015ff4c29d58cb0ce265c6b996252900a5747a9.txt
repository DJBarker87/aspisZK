import R1Z.PV_CB_Op80Types
import R1Z.PV_CB_State
set_option autoImplicit false
namespace R1Z.PV_CB_Op80Transport
abbrev Native (E : Type) := ProverRwFull.aspis_core.r0.scalar.CodeField E
abbrev Raw (E : Type) := PV_CB_ShippedOp80.aspis_core.r0.scalar.CodeField E
def encode {E : Type} (x : Native E) : Raw E := {
  ZERO := x.ZERO
  ONE := x.ONE
  coremarkerCopyInst := x.coremarkerCopyInst
  corecmpEqInst := x.corecmpEqInst
  from_m31 := x.from_m31
  add := x.add
  sub := x.sub
  neg := x.neg
  mul := x.mul
  try_inv := x.try_inv
}
def decode {E : Type} (x : Raw E) : Native E := {
  ZERO := x.ZERO
  ONE := x.ONE
  coremarkerCopyInst := x.coremarkerCopyInst
  corecmpEqInst := x.corecmpEqInst
  from_m31 := x.from_m31
  add := x.add
  sub := x.sub
  neg := x.neg
  mul := x.mul
  try_inv := x.try_inv
}
theorem native_roundtrip {E : Type} (x : Native E) : decode (encode x) = x := by cases x; rfl
theorem extracted_roundtrip {E : Type} (x : Raw E) : encode (decode x) = x := by cases x; rfl
#print axioms native_roundtrip
#print axioms extracted_roundtrip
end R1Z.PV_CB_Op80Transport
