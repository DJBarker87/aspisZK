import LPi_Total
set_option autoImplicit false
namespace AspisR1.LPi_NatBase
open Aeneas Aeneas.Std Result

theorem sub_word (x y : U32) (h : y.val ≤ x.val) :
    (U32.wrapping_sub x y).val = x.val-y.val := by
  rw [U32.wrapping_sub_val_eq]
  have hx := x.hSize
  have hy := y.hSize
  have he : x.val+(UScalar.size .U32-y.val)=(x.val-y.val)+UScalar.size .U32 := by omega
  rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]

theorem add (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.add x y = ok z ∧
    z.val = (x.val+y.val)%2147483647 ∧ z.val < 2147483647 := by
  let s := U32.wrapping_add x y
  have sv : s.val = x.val+y.val := by
    rw [U32.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
  simp only [FIo_Native.aspis_core.field.M31.add,FIo_Native.aspis_core.field.P,lift,bind_tc_ok]
  change ∃ z, (if s ≥ 2147483647#u32 then
    ok (U32.wrapping_sub s 2147483647#u32) else ok s) = ok z ∧ _
  by_cases h : s ≥ 2147483647#u32
  · rw [if_pos h]
    have hp : 2147483647 ≤ s.val := by scalar_tac
    refine ⟨_,rfl,?_,?_⟩
    · rw [sub_word s 2147483647#u32 hp]
      change s.val-2147483647 = (x.val+y.val)%2147483647
      rw [sv,Nat.mod_eq_sub_mod hp,Nat.mod_eq_of_lt (by omega)]
    · rw [sub_word s 2147483647#u32 hp]; change s.val-2147483647 < 2147483647; omega
  · rw [if_neg h]
    have hp : s.val < 2147483647 := by scalar_tac
    exact ⟨_,rfl,by rw [←sv,Nat.mod_eq_of_lt hp],hp⟩

theorem sub (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.sub x y = ok z ∧
    z.val = (x.val+2147483647-y.val)%2147483647 ∧ z.val < 2147483647 := by
  let a := U32.wrapping_add x 2147483647#u32
  have av : a.val = x.val+2147483647 := by
    rw [U32.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
    rfl
  let s := U32.wrapping_sub a y
  have sv : s.val = x.val+2147483647-y.val := by
    rw [sub_word _ _ (by omega),av]
  simp only [FIo_Native.aspis_core.field.M31.sub,FIo_Native.aspis_core.field.P,lift,bind_tc_ok]
  change ∃ z, (if s ≥ 2147483647#u32 then
    ok (U32.wrapping_sub s 2147483647#u32) else ok s) = ok z ∧ _
  by_cases h : s ≥ 2147483647#u32
  · rw [if_pos h]
    have hp : 2147483647 ≤ s.val := by scalar_tac
    refine ⟨_,rfl,?_,?_⟩
    · rw [sub_word s 2147483647#u32 hp]
      change s.val-2147483647 = (x.val+2147483647-y.val)%2147483647
      rw [←sv,Nat.mod_eq_sub_mod hp,Nat.mod_eq_of_lt (by omega)]
    · rw [sub_word s 2147483647#u32 hp]; change s.val-2147483647 < 2147483647; omega
  · rw [if_neg h]
    have hp : s.val < 2147483647 := by scalar_tac
    exact ⟨_,rfl,by rw [←sv,Nat.mod_eq_of_lt hp],hp⟩

#print axioms sub_word
#print axioms add
#print axioms sub
end AspisR1.LPi_NatBase
