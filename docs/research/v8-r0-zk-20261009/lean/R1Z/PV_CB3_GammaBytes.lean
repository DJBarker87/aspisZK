import R1Z.PV_CB3_GammaBounds
import R1Z.PV_CB3_DigitBlocks
namespace R1Z.PV_CB3_GammaBytes
open PV_CB3_SamplerCarry PV_CB3_SamplerWord PV_CB3_GammaRank
set_option autoImplicit false

/-- Rank formula at the byte-loading boundary, for eight arbitrary four-byte
blocks. This mathematical transport has no desired-output premise. -/
theorem byte_formula (chunks : List (List Nat)) (count : chunks.length = 8)
    (width : ∀ c, c ∈ chunks → c.length = 4)
    (bytes : ∀ c, c ∈ chunks → ∀ d, d ∈ c → d < 256) :
    value base (sampleDigits base radix 8 (chunks.map (value 256))) =
      value 256 chunks.flatten % (base ^ 8 - 1) + 1 := by
  have hr : (256 : Nat) ^ 4 = radix := by decide
  have canonical := PV_CB3_DigitBlocks.grouped_canonical 256 4 chunks width bytes
  rw [hr] at canonical
  rw [PV_CB3_GammaBounds.rank_formula _ (by simpa only [List.length_map] using count) canonical]
  have ranks := PV_CB3_DigitBlocks.grouped_value 256 4 chunks width
  rw [hr] at ranks
  rw [ranks]

#print axioms byte_formula
end R1Z.PV_CB3_GammaBytes
