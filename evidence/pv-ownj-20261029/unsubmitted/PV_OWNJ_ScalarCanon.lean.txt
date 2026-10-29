import R1Z.PV_OWNJ_ScalarDecode
set_option autoImplicit false
namespace R1Z.PV_OWNJ_ScalarCanon
open Aeneas.Std PV_OWNJ_ScalarDecode

theorem add_canon (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
 (add a b).val < 2147483647 := by
 rw [add_decode a b ha hb]
 exact Nat.mod_lt _ (by omega)

theorem sub_canon (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
 (sub a b).val < 2147483647 := by
 rw [sub_decode a b ha hb]
 exact Nat.mod_lt _ (by omega)

#print axioms add_canon
#print axioms sub_canon
end R1Z.PV_OWNJ_ScalarCanon
