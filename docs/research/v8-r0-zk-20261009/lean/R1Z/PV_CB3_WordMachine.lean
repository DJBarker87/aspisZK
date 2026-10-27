import R1Z.PV_CB3_WordBits
namespace R1Z.PV_CB3_WordMachine
open PV_CB3_SamplerWord
set_option autoImplicit false

/-- Machine arithmetic view of the extracted word step. The Aeneas Result
connection remains in PV_CB3_SamplerWordSource; this view exposes bit widths. -/
def denominator : BitVec 64 := BitVec.ofNat 64 base
def step (word : BitVec 32) (prior : BitVec 64) : BitVec 32 × BitVec 64 :=
  let n := (prior <<< 32) ||| word.setWidth 64
  ((n / denominator).setWidth 32, n % denominator)

theorem denominator_value : denominator.toNat = base := by rfl

theorem remainder_value (word : BitVec 32) (prior : BitVec 64)
    (canonical : prior.toNat < base) :
    (step word prior).2.toNat = dividend prior.toNat word.toNat % base := by
  dsimp only [step]
  rw [BitVec.toNat_umod, denominator_value,
    PV_CB3_WordBits.dividend_bits prior word (by
      have h : base < radix := by unfold base radix; omega
      omega)]

theorem quotient_value (word : BitVec 32) (prior : BitVec 64)
    (canonical : prior.toNat < base) :
    (step word prior).1.toNat = dividend prior.toNat word.toNat / base := by
  have hw : word.toNat < radix := word.isLt
  have hq := quotient_word_bound prior.toNat word.toNat canonical hw
  dsimp only [step]
  rw [BitVec.toNat_setWidth, BitVec.toNat_udiv, denominator_value,
    PV_CB3_WordBits.dividend_bits prior word (by
      have h : base < radix := by unfold base radix; omega
      omega)]
  exact Nat.mod_eq_of_lt hq

theorem remainder_canonical (word : BitVec 32) (prior : BitVec 64)
    (canonical : prior.toNat < base) : (step word prior).2.toNat < base := by
  rw [remainder_value word prior canonical]
  exact canonical_remainder _ _

#print axioms denominator_value
#print axioms remainder_value
#print axioms quotient_value
#print axioms remainder_canonical
end R1Z.PV_CB3_WordMachine
