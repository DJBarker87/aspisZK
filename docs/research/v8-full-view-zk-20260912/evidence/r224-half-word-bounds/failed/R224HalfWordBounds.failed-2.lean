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
  have h1 : (1 : BitVec 32).toNat=1 := rfl
  simp only [halfWord,BitVec.toNat_or,BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft,BitVec.toNat_and,h1,
    Nat.and_one_is_mod,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq]
  norm_num
  rcases hr with hr | hr
  · simp [hr]
  · simp only [hr,one_mul]
    exact Nat.or_two_pow_eq_add_of_lt hd

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
  have h0 : (0 : BitVec 32).toNat=0 := rfl
  have hp : (2147483647#32).toNat=2147483647 := rfl
  by_cases hb : w &&& 1 = 0
  · have hz := he.mp hb
    simp only [if_pos hb,BitVec.toNat_add,value w h,h0,hz,zero_mul,add_zero]
    apply congrArg (fun n : Nat => n % 2^32)
    omega
  · have ho : w.toNat%2=1 := by
      have hn : w.toNat%2≠0 := fun hz => hb (he.mpr hz)
      omega
    simp only [if_neg hb,BitVec.toNat_add,value w h,hp,ho,one_mul]
    apply congrArg (fun n : Nat => n % 2^32)
    omega

#print axioms value
#print axioms canonical
#print axioms double_word
end AspisV8R19.R224HalfWordBounds
