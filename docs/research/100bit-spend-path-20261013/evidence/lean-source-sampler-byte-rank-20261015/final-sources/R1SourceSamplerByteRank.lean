import R1SamplerBlockRank
import R1SamplerBytePass
import R1SamplerRepeatedPass

/-! Compose the checked byte-to-word, positional-rank, and repeated-pass
identities for a fixed 32-byte Aeneas array. These are arithmetic/model
identities only; they do not assert the Rust sampler loop or a source-level
sampler correspondence. -/
set_option autoImplicit false

namespace AspisR1.SourceSamplerByteRank

open Aeneas Aeneas.Std
open AspisR1.SamplerMachineBounds
open AspisR1.SamplerBytePass
open AspisR1.SamplerRepeatedPass
open AspisR1.SamplerNatModel
open AspisR1.SamplerAddBridge

def rank (b : Array U8 32#usize) : Nat :=
  (R0C.ModuloField.blockRank (AspisV8R19.SqueezeOracleBridge.decodeState b)).val

/-- The eight decoded bytes words, interpreted by the existing high-to-low
base-`B` numeral, equal the positional rank of the source-shaped 32 bytes. -/
theorem word_value (b : Array U8 32#usize) :
    SamplerRepeatedPass.wordValue (SamplerBytePass.digits b) = rank b := by
  unfold SamplerRepeatedPass.wordValue
  rw [SamplerBytePass.digits_values]
  exact SamplerBlockRank.word_numeral_eq_rank
    (AspisV8R19.SqueezeOracleBridge.decodeState b)

/-- Every repeated pass over the decoded words agrees with the Nat low-digit
model at the block-rank value. -/
theorem run_bytes (n : Nat) (b : Array U8 32#usize) :
    (SamplerRepeatedPass.run n (SamplerBytePass.digits b)).1 =
      SamplerNatModel.lowDigits P n (rank b) := by
  rw [SamplerRepeatedPass.run_digits, word_value]

theorem run4_bytes (b : Array U8 32#usize) :
    (SamplerRepeatedPass.run 4 (SamplerBytePass.digits b)).1 =
      SamplerNatModel.qm31Digits (rank b) := by
  simpa [SamplerNatModel.qm31Digits] using run_bytes 4 b

theorem run8_bytes (b : Array U8 32#usize) :
    (SamplerRepeatedPass.run 8 (SamplerBytePass.digits b)).1 =
      SamplerNatModel.ordinaryDigits (rank b) := by
  simpa [SamplerNatModel.ordinaryDigits] using run_bytes 8 b

theorem remaining8_value (b : Array U8 32#usize) :
    SamplerRepeatedPass.wordValue
        (SamplerRepeatedPass.run 8 (SamplerBytePass.digits b)).2 =
      rank b / P ^ 8 := by
  rw [SamplerRepeatedPass.run_remaining, word_value]

/-- End-around carry applied to the eight machine-model remainders and their
remaining quotient, written as the explicit `Nat` digit model. -/
def gammaBytes (b : Array U8 32#usize) : List Nat :=
  SamplerAddBridge.endAround P
    (SamplerRepeatedPass.wordValue
      (SamplerRepeatedPass.run 8 (SamplerBytePass.digits b)).2)
    (SamplerRepeatedPass.run 8 (SamplerBytePass.digits b)).1

theorem gammaBytes_eq_gammaDigits (b : Array U8 32#usize) :
    gammaBytes b = SamplerNatModel.gammaDigits (rank b) := by
  unfold gammaBytes SamplerNatModel.gammaDigits SamplerNatModel.ordinaryDigits
  rw [remaining8_value, run8_bytes]
  rfl

theorem rank_lt (b : Array U8 32#usize) : rank b < 2 ^ 256 := by
  have h := (R0C.ModuloField.blockRank
    (AspisV8R19.SqueezeOracleBridge.decodeState b)).isLt
  have hpow : 256 ^ 32 = 2 ^ 256 := by norm_num
  calc
    rank b < 256 ^ 32 := h
    _ = 2 ^ 256 := hpow

/-- The byte-derived end-around digit value has the same mathematical value
as the existing gamma Nat model. -/
theorem gammaBytes_value (b : Array U8 32#usize) :
    SamplerAddDigits.digitsValue P (gammaBytes b) =
      rank b % (P ^ 8 - 1) + 1 := by
  rw [gammaBytes_eq_gammaDigits]
  exact SamplerNatModel.gammaDigits_value (rank_lt b)

#print axioms word_value
#print axioms run_bytes
#print axioms run4_bytes
#print axioms run8_bytes
#print axioms remaining8_value
#print axioms gammaBytes_eq_gammaDigits
#print axioms gammaBytes_value

end AspisR1.SourceSamplerByteRank
