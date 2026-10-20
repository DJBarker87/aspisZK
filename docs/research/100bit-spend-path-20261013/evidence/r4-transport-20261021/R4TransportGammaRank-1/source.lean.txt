import R4TransportGammaFold

/-! Concrete 256-bit domain for the optimized gamma arithmetic specification.
No source digit-array invariant or exact-wide decoder identity is assumed proved. -/
set_option autoImplicit false
namespace AspisR1.R4TransportGammaRank
open R4TransportGammaFold

def p8 : Nat := 2147483647^8

theorem quotient_bound (x : Nat) (hx : x < 2^256) : x / p8 < 257 := by
  have hpos : 0 < p8 := by norm_num [p8]
  apply (Nat.div_lt_iff_lt_mul hpos).2
  exact lt_of_lt_of_le hx (by norm_num [p8])

theorem gamma_rank (x : Nat) (hx : x < 2^256) :
    folded x p8 = x % (p8 - 1) + 1 := by
  have hq := quotient_bound x hx
  have hm : 259 < p8 := by norm_num [p8]
  exact folded_eq_nonzero_rank x p8 (by omega) (by omega)

theorem gamma_rank_canonical_nonzero (x : Nat) (hx : x < 2^256) :
    0 < folded x p8 ∧ folded x p8 < p8 := by
  rw [gamma_rank x hx]
  have hm : 1 < p8 := by norm_num [p8]
  have hr := Nat.mod_lt x (show 0 < p8 - 1 by omega)
  omega

#print axioms quotient_bound
#print axioms gamma_rank
#print axioms gamma_rank_canonical_nonzero
end AspisR1.R4TransportGammaRank
