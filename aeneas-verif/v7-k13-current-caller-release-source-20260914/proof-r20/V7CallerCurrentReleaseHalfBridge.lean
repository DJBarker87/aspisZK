import V7CallerCurrentReleaseFieldBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7CallerCurrentReleaseHalfBridge

open V7CallerCurrentReleaseFieldBridge

abbrev M31 := V7CallerCurrentReleaseR20.field.M31
abbrev QM31 := V7CallerCurrentReleaseR20.field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseFieldBridge.ExactM31
abbrev ExactCM31 := V7CallerCurrentReleaseFieldBridge.ExactCM31
abbrev ExactQM31 := V7CallerCurrentReleaseFieldBridge.ExactQM31

def rawHalf (x : Nat) : Nat :=
  if x % 2 = 0 then x / 2 else x / 2 + 2 ^ 30

private theorem shiftRightOneVal (x : Std.U32) :
    (Std.U32.wrapping_shr x 1#u32).val = x.val / 2 := by
  change (x.bv.ushiftRight (1 % 32)).toNat = x.bv.toNat / 2
  norm_num [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem bitAndOneVal (x : Std.U32) :
    (x &&& 1#u32).val = x.val % 2 := by
  simp only [UScalar.val_and, UScalar.ofNatCore_val_eq, Nat.and_one_is_mod]

private theorem shiftedParityVal (x : Std.U32) :
    (Std.U32.wrapping_shl (x &&& 1#u32) 30#u32).val =
      (x.val % 2) * 2 ^ 30 := by
  rcases Nat.mod_two_eq_zero_or_one x.val with h | h
  · have hx : x &&& 1#u32 = 0#u32 := by
      apply UScalar.eq_of_val_eq
      simpa [bitAndOneVal] using h
    rw [hx, h]
    change ((BitVec.ofNat 32 0) <<< (30 % 32)).toNat = 0
    norm_num
  · have hx : x &&& 1#u32 = 1#u32 := by
      apply UScalar.eq_of_val_eq
      simpa [bitAndOneVal] using h
    rw [hx, h]
    change ((BitVec.ofNat 32 1) <<< (30 % 32)).toNat = 1073741824
    norm_num [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private theorem currentHalfVal
    (x : M31)
    (hx : AspisAeneasCM31Multiplicative.CanonicalRawM31 x.val) :
    ((
      (Std.U32.wrapping_shr x 1#u32)
      ||| Std.U32.wrapping_shl (x &&& 1#u32) 30#u32)).val = rawHalf x.val := by
  rw [UScalar.val_or, shiftRightOneVal, shiftedParityVal]
  rcases Nat.mod_two_eq_zero_or_one x.val with h | h
  · simp [rawHalf, h]
  · have hhalf : x.val / 2 < 2 ^ 30 := by
      unfold AspisAeneasCM31Multiplicative.CanonicalRawM31 at hx
      norm_num at hx ⊢
      omega
    rw [rawHalf, if_neg (by omega), h]
    norm_num
    have hor := Nat.two_pow_add_eq_or_of_lt hhalf 1
    norm_num at hor
    calc
      x.val / 2 ||| 1073741824 = 1073741824 ||| x.val / 2 := Nat.or_comm _ _
      _ = 1073741824 + x.val / 2 := hor.symm
      _ = x.val / 2 + 1073741824 := Nat.add_comm _ _

private theorem rawHalfCanonical
    {x : Nat} (hx : x < 2147483647) : rawHalf x < 2147483647 := by
  unfold rawHalf
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h] <;> omega

private theorem rawHalfDouble
    {x : Nat} (hx : x < 2147483647) :
    (2 : ExactM31) * (rawHalf x : ExactM31) = (x : ExactM31) := by
  unfold rawHalf
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [if_pos h]
    have hdouble : 2 * (x / 2) = x := by omega
    have hc := congrArg (fun n : Nat => (n : ExactM31)) hdouble
    rw [Nat.cast_mul] at hc
    norm_num at hc ⊢
    exact hc
  · rw [if_neg (by omega)]
    have hdouble : 2 * (x / 2 + 2 ^ 30) = x + 2147483647 := by
      norm_num at hx ⊢
      omega
    change ((2 : Nat) : ExactM31) *
      ((x / 2 + 2 ^ 30 : Nat) : ExactM31) = (x : ExactM31)
    rw [← Nat.cast_mul, hdouble, Nat.cast_add, ZMod.natCast_self, add_zero]

private theorem generated_m31_half_corresponds
    (x : M31)
    (hx : AspisAeneasCM31Multiplicative.CanonicalRawM31 x.val) :
    ∃ out : M31,
      V7CallerCurrentReleaseR20.field.M31.half x = ok out ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ExactM31) + ((out.val : Nat) : ExactM31) =
        (x.val : ExactM31) := by
  let out := (Std.U32.wrapping_shr x 1#u32) |||
    Std.U32.wrapping_shl (x &&& 1#u32) 30#u32
  have hout : out.val = rawHalf x.val := currentHalfVal x hx
  refine ⟨out, ?_, ?_, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.M31.half, Std.lift, bind_tc_ok, out]
  · rw [hout]
    exact rawHalfCanonical hx
  · rw [hout, ← two_mul]
    exact rawHalfDouble hx

private theorem generated_cm31_half_corresponds
    (x : V7CallerCurrentReleaseR20.field.CM31)
    (hx : GeneratedCanonicalCM31 x) :
    ∃ out : V7CallerCurrentReleaseR20.field.CM31,
      V7CallerCurrentReleaseR20.field.CM31.half x = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out + generatedCm31ToExact out =
        generatedCm31ToExact x := by
  obtain ⟨a, ha, hca, hea⟩ := generated_m31_half_corresponds x.a hx.1
  obtain ⟨b, hb, hcb, heb⟩ := generated_m31_half_corresponds x.b hx.2
  let out : V7CallerCurrentReleaseR20.field.CM31 := ⟨a, b⟩
  refine ⟨out, ?_, ⟨hca, hcb⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.CM31.half, ha, hb, out]
  · apply QuadraticAlgebra.ext
    · exact hea
    · exact heb

theorem generated_qm31_half_corresponds
    (x : QM31) (hx : GeneratedCanonicalQM31 x) :
    ∃ out : QM31,
      V7CallerCurrentReleaseR20.field.QM31.half x = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out + generatedQm31ToExact out =
        generatedQm31ToExact x := by
  obtain ⟨c0, hc0, hcc0, he0⟩ := generated_cm31_half_corresponds x.c0 hx.1
  obtain ⟨c1, hc1, hcc1, he1⟩ := generated_cm31_half_corresponds x.c1 hx.2
  let out : QM31 := ⟨c0, c1⟩
  refine ⟨out, ?_, ⟨hcc0, hcc1⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR20.field.QM31.half, hc0, hc1, out]
  · apply QuadraticAlgebra.ext
    · exact he0
    · exact he1

#print axioms generated_qm31_half_corresponds

end V7CallerCurrentReleaseHalfBridge
