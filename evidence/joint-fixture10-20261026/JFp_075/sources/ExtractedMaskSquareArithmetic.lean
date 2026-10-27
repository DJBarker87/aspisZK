import AspisV8R17.RawReducerNat

/-! Pure arithmetic bridge adapted from the proof bodies in
`GeneratedCM31SquareNormalized.lean` (historical source SHA
`d100cd8da24014e36b23d188cfb9c0958480b1ec882244ba2805275d6a9e2d5a`).
Only Nat/Int identities are reproduced here; no old generated runtime is
imported into the current extraction graph. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskSquareArithmetic

abbrev P : Nat := AspisV8R17.RawReducer.P

theorem square_real_int (a b : Nat) (hb : b < P) :
    ((((a + b) * (a + P - b)) % P : Nat) : Int) =
      ((a : Int) * a - (b : Int) * b) % (P : Int) := by
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  have hbb := Nat.mul_le_mul_right b (Nat.le_of_lt hb)
  unfold P AspisV8R17.RawReducer.P at *
  simp only [Nat.mul_sub_left_distrib, Nat.add_mul, Nat.mul_add,
    Nat.mul_comm b a]
  omega

def imagWord (a b c d : Nat) :=
  ((((a + b) * (c + d)) % P + P - (a * c) % P) % P + P -
    (b * d) % P) % P

theorem imagWord_mod (a b c d : Nat) :
    imagWord a b c d = (a * d + b * c) % P := by
  unfold imagWord P AspisV8R17.RawReducer.P
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-- Pure specialization of the retained GeneratedCM31Normalized.realWord_int
proof body; the old generated runtime is not imported. -/
theorem mul_self_real_int (a b : Nat) :
    ((((a * a) % P + P - (b * b) % P) % P : Nat) : Int) =
      ((a : Int) * a - (b : Int) * b) % (P : Int) := by
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  unfold P AspisV8R17.RawReducer.P
  omega

theorem square_real_word_eq_mul_self_real (a b : Nat)
    (ha : a < P) (hb : b < P) :
    ((a + b) * (a + P - b)) % P =
      ((a * a) % P + P - (b * b) % P) % P := by
  have hleft := square_real_int a b hb
  have hright := mul_self_real_int a b
  omega

#print axioms square_real_int
#print axioms imagWord_mod
#print axioms mul_self_real_int
#print axioms square_real_word_eq_mul_self_real

end AspisR1.ExtractedMaskSquareArithmetic
