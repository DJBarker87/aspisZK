import Mathlib.Tactic

/-! Kernel-checked finite-width predecessor for selected M31 half.
No source half-method execution identity is asserted here. -/
set_option autoImplicit false
namespace AspisV8R19.R224HalfWordBounds

def halfWord (w : BitVec 32) : BitVec 32 :=
  (w >>> 1) ||| ((w &&& 1) <<< 30)

theorem value (w : BitVec 32) (h : w < 2147483647#32) :
    (halfWord w).toNat = w.toNat/2+(w.toNat%2)*1073741824 := by
  have hw : w.toNat < 2147483647 := h
  have hd : w.toNat/2 < 2^30 := by norm_num; omega
  have hm : w.toNat%2 < 2 := Nat.mod_lt _ (by decide)
  have hr : w.toNat%2=0 ∨ w.toNat%2=1 := by omega
  simp only [halfWord,BitVec.toNat_or,BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft,BitVec.toNat_and,BitVec.toNat_ofNat,
    Nat.and_one_is_mod,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq]
  norm_num
  rcases hr with hr | hr
  · simp [hr]
  · simp only [hr,one_mul]
    rw [Nat.or_two_pow_eq_add_of_lt hd]
    rfl

theorem canonical (w : BitVec 32) (h : w < 2147483647#32) :
    halfWord w < 2147483647#32 := by
  change (halfWord w).toNat < 2147483647
  rw [value w h]
  have hw : w.toNat < 2147483647 := h
  have hd := Nat.mod_add_div w.toNat 2
  have hm := Nat.mod_lt w.toNat (by decide : 0<2)
  omega

theorem double_word (w : BitVec 32) (h : w < 2147483647#32) :
    halfWord w + halfWord w =
      w + (if w &&& 1 = 0 then 0 else 2147483647#32) := by
  apply BitVec.eq_of_toNat_eq
  have he : (w &&& 1 = 0) ↔ w.toNat%2=0 := by
    rw [← BitVec.toNat_inj]
    simp [BitVec.toNat_and,Nat.and_one_is_mod]
  have hd := Nat.mod_add_div w.toNat 2
  have hm := Nat.mod_lt w.toNat (by decide : 0<2)
  by_cases hz : w.toNat%2=0
  · simp only [he,hz,if_true,BitVec.toNat_add,value w h,
      BitVec.toNat_ofNat,zero_mul,add_zero]
    congr 1
    omega
  · have ho : w.toNat%2=1 := by omega
    simp only [he,hz,if_false,BitVec.toNat_add,value w h,
      BitVec.toNat_ofNat,ho,one_mul]
    congr 1
    omega

#print axioms value
#print axioms canonical
#print axioms double_word
end AspisV8R19.R224HalfWordBounds
