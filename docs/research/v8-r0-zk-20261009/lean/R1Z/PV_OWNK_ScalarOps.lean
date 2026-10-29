import R1Z.PV_OWNK_CTDecode
set_option autoImplicit false
namespace R1Z.PV_OWNK_ScalarOps
open Aeneas Aeneas.Std
abbrev M := PV_B2_FieldValue.aspis_core.field.M31
abbrev Canon (x : U32) : Prop := x.val < 2147483647

theorem mul_canon (a b : U32) : Canon (PV_B2_FieldValue.aspis_core.field.M31.mul a b) :=
 PV_OWNK_CTDecode.reduce_canon _

theorem mul_decode (a b : U32) :
 (PV_B2_FieldValue.aspis_core.field.M31.mul a b).val = (a.val*b.val) % 2147483647 := by
 have ha : a.val < 4294967296 := a.hBounds
 have hb : b.val < 4294967296 := b.hBounds
 have hac : (UScalar.cast .U64 a).val = a.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by change a.val < 18446744073709551616; omega)
 have hbc : (UScalar.cast .U64 b).val = b.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by change b.val < 18446744073709551616; omega)
 have hp : a.val*b.val < 18446744073709551616 := by
  change a.val < 4294967296 at ha
  change b.val < 4294967296 at hb
  nlinarith
 unfold PV_B2_FieldValue.aspis_core.field.M31.mul
  PV_B2_FieldValue.aspis_core.field.reduce_u64
 rw [PV_OWNK_CTDecode.reduce_decode,U64.wrapping_mul_val_eq,hac,hbc,UScalar.size]
 rw [Nat.mod_eq_of_lt hp]

theorem reduce_canon (a : U64) : Canon (PV_B2_FieldValue.aspis_core.field.M31.reduce_u64 a) :=
 PV_OWNK_CTDecode.reduce_canon _

theorem add_canon (a b : U32) (ha : Canon a) (hb : Canon b) : Canon (PV_B2_FieldValue.aspis_core.field.M31.add a b) :=
 PV_OWNK_CTDecode.add_canon a b ha hb

theorem sub_canon (a b : U32) (ha : Canon a) (hb : Canon b) : Canon (PV_B2_FieldValue.aspis_core.field.M31.sub a b) :=
 PV_OWNK_CTDecode.sub_canon a b ha hb

theorem double_canon (a : U32) (ha : Canon a) : Canon (PV_B2_FieldValue.aspis_core.field.M31.double a) := add_canon a a ha ha

#print axioms mul_canon
#print axioms mul_decode
#print axioms reduce_canon
#print axioms add_canon
#print axioms sub_canon
#print axioms double_canon
end R1Z.PV_OWNK_ScalarOps
