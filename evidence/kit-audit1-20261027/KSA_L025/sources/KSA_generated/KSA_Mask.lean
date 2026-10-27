import KSA_Checks
open Aeneas Aeneas.Std Result XRn_Join_Release XRn_Join_FieldExternal
set_option autoImplicit false
namespace KSA

def scalar (n : U32) : aspis_core.field.QM31 := ⟨⟨n,0#u32⟩,⟨0#u32,0#u32⟩⟩
-- Tiny recursion spine: 26 -> 12 -> 5 -> 2 -> 0. No huge exponent.
theorem qpow26 : XRn_Join_qpow (scalar 275#u32) 26 = ok (scalar 1424173331#u32) := by
  simp [XRn_Join_qpow,scalar,qone,aspis_core.field.QM31.mul,
    XRn_Join_Field.field.QM31.mul,XRn_Join_Field.field.CM31.mul,
    XRn_Join_Field.field.CM31.add,XRn_Join_Field.field.CM31.sub,
    XRn_Join_Field.field.M31.mul,XRn_Join_Field.field.M31.add,
    XRn_Join_Field.field.M31.sub,XRn_Join_Field.field.M31.reduce_u64,
    XRn_Join_Field.field.reduce_u64,XRn_Join_Field.field.mul_by_r,
    XRn_Join_Field.field.P,bind_tc_ok]
#print axioms qpow26
end KSA
