import R1Z.PV_OWNK_ScalarOps
import AspisV8R15.ExactTowerBase
import Mathlib.Tactic.Ring
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNK_FieldScalar
open Aeneas Aeneas.Std
open PV_OWNK_ScalarOps
abbrev F := AspisV8R15.ExactTowerBase.M31Exact
def decode (x : U32) : F := x.val

theorem add (a b : U32) (ha : Canon a) (hb : Canon b) :
 decode (M.add a b) = decode a + decode b := by
 change ((PV_OWNK_CTDecode.add a b).val : F) = _
 rw [PV_OWNK_CTDecode.add_decode a b ha hb,ZMod.natCast_mod,Nat.cast_add]
 rfl
theorem sub (a b : U32) (ha : Canon a) (hb : Canon b) :
 decode (M.sub a b) = decode a - decode b := by
 change ((PV_OWNK_CTDecode.sub a b).val : F) = _
 rw [PV_OWNK_CTDecode.sub_decode a b ha hb,ZMod.natCast_mod,
  Nat.cast_sub (show b.val ≤ a.val+2147483647 by unfold Canon at hb; omega),Nat.cast_add]
 rw [show (2147483647 : F)=0 from ZMod.natCast_self 2147483647,add_zero]
 rfl
theorem mul (a b : U32) : decode (M.mul a b) = decode a * decode b := by
 unfold decode
 rw [mul_decode,ZMod.natCast_mod,Nat.cast_mul]
theorem reduce (a : U64) : decode (M.reduce_u64 a) = (a.val : F) := by
 unfold decode M PV_B2_FieldValue.aspis_core.field.M31.reduce_u64
  PV_B2_FieldValue.aspis_core.field.reduce_u64
 rw [PV_OWNK_CTDecode.reduce_decode,ZMod.natCast_mod]
theorem double (a : U32) (ha : Canon a) : decode (M.double a) = decode a + decode a :=
 add a a ha ha
#print axioms add
#print axioms sub
#print axioms mul
#print axioms reduce
#print axioms double
end R1Z.PV_OWNK_FieldScalar
