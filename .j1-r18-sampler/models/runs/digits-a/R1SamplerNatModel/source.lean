import R1SamplerAddBridge
import R1SamplerMachineBounds
import R1SamplerPass
import R1SamplerRanking

/-! The sampler's chosen 4/8-digit algorithms as Nat/list models. The modulo
laws and parameter bounds are conclusions, not premises. This does not prove
byte packing, fixed-width operations, field-tuple decoding, or Rust refinement. -/
set_option autoImplicit false
namespace AspisR1.SamplerNatModel
open AspisR1.SamplerDigits AspisR1.SamplerAddDigits AspisR1.SamplerAddBridge
open AspisR1.SamplerArithmetic AspisR1.SamplerMachineBounds

/-- Repeated low-digit extraction by quotient and remainder. -/
def lowDigits (p : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, x => x % p :: lowDigits p n (x / p)

theorem lowDigits_length (p n x : Nat) : (lowDigits p n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [lowDigits, ih]

theorem lowDigits_canonical {p : Nat} (hp : 0 < p) (n x : Nat) :
    ∀ d ∈ lowDigits p n x, d < p := by
  induction n generalizing x with
  | zero => simp [lowDigits]
  | succ n ih =>
    intro d hd
    simp only [lowDigits, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ hp
    · exact ih _ d hd

theorem lowDigits_value (p n x : Nat) :
    digitsValue p (lowDigits p n x) = lowValue p n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [lowDigits, digitsValue, lowValue, ih]

def qm31Digits (x : Nat) : List Nat := lowDigits P 4 x
def ordinaryDigits (x : Nat) : List Nat := lowDigits P 8 x
def gammaDigits (x : Nat) : List Nat :=
  endAround P (x / P ^ 8) (ordinaryDigits x)

theorem qm31Digits_value (x : Nat) :
    digitsValue P (qm31Digits x) = x % P ^ 4 := by
  rw [qm31Digits, lowDigits_value, lowValue_eq_mod_pow P_pos]

theorem ordinaryDigits_value (x : Nat) :
    digitsValue P (ordinaryDigits x) = x % P ^ 8 := by
  rw [ordinaryDigits, lowDigits_value, lowValue_eq_mod_pow P_pos]

/-- The explicit low-digit tuple ranks to the same remainder as the list
algorithm, using the checked finite positional equivalence. -/
theorem qm31Digits_positionalRank (x : Nat) :
    (AspisR1.SamplerRanking.digitsRank P 4
      (AspisR1.SamplerRanking.canonicalDigits P 4 x P_pos)).val =
      digitsValue P (qm31Digits x) := by
  rw [AspisR1.SamplerRanking.canonicalDigits_eq_rank_symm,
    Equiv.apply_symm_apply]
  exact (qm31Digits_value x).symm

theorem ordinaryDigits_positionalRank (x : Nat) :
    (AspisR1.SamplerRanking.digitsRank P 8
      (AspisR1.SamplerRanking.canonicalDigits P 8 x P_pos)).val =
      digitsValue P (ordinaryDigits x) := by
  rw [AspisR1.SamplerRanking.canonicalDigits_eq_rank_symm,
    Equiv.apply_symm_apply]
  exact (ordinaryDigits_value x).symm

theorem gammaDigits_value {x : Nat} (hx : x < 2 ^ 256) :
    digitsValue P (gammaDigits x) = x % (P ^ 8 - 1) + 1 := by
  have hlen : (ordinaryDigits x).length = 8 := lowDigits_length P 8 x
  have hv := endAround_value P_pos (ordinaryDigits x)
    (lowDigits_canonical P_pos 8 x)
    (by rw [hlen]; exact two_le_P8)
    (by rw [hlen]; exact rank_div_P8_lt_P8_sub_one hx)
  rw [hlen, ordinaryDigits, lowDigits_value] at hv
  change digitsValue P (gammaDigits x) = _ at hv
  rw [hv]
  exact (gammaRank_eq_mod P_pos two_le_P8 (rank_div_P8_lt_P8_sub_one hx)).1

theorem gammaDigits_value_bounds {x : Nat} (hx : x < 2 ^ 256) :
    0 < digitsValue P (gammaDigits x) ∧
      digitsValue P (gammaDigits x) < P ^ 8 := by
  rw [gammaDigits_value hx]
  have hmod := Nat.mod_lt x (show 0 < P ^ 8 - 1 by have := two_le_P8; omega)
  omega

theorem gammaDigits_canonical (x : Nat) :
    (gammaDigits x).length = 8 ∧ ∀ d ∈ gammaDigits x, d < P := by
  unfold gammaDigits endAround
  dsimp only
  split_ifs
  · exact ⟨by rw [addDigits_length]; exact lowDigits_length P 8 x,
      addDigits_output_digits_lt P _ _ P_pos⟩
  · exact ⟨by rw [addDigits_length, addDigits_length]; exact lowDigits_length P 8 x,
      addDigits_output_digits_lt P _ _ P_pos⟩

/-- Each long-division pass of the Nat state model computes the quotient and
remainder used by lowDigits, when given the high-to-low radix-2^32 word list. -/
theorem radix32_pass (digits : List Nat) (hcan : ∀ d ∈ digits, d < B) :
    let state := AspisR1.SamplerLongDivision.process B P
      AspisR1.SamplerLongDivision.initialState digits
    state.quotient = AspisR1.SamplerPass.numeral B digits / P ∧
      state.remainder = AspisR1.SamplerPass.numeral B digits % P :=
  AspisR1.SamplerPass.initialState_process_quotient_remainder B_pos P_pos digits hcan

#print axioms lowDigits_length
#print axioms lowDigits_canonical
#print axioms lowDigits_value
#print axioms qm31Digits_value
#print axioms ordinaryDigits_value
#print axioms qm31Digits_positionalRank
#print axioms ordinaryDigits_positionalRank
#print axioms gammaDigits_value
#print axioms gammaDigits_value_bounds
#print axioms gammaDigits_canonical
#print axioms radix32_pass
end AspisR1.SamplerNatModel
