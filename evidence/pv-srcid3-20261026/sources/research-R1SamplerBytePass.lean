import R1SamplerByteWord
import R1SamplerWordPass

set_option autoImplicit false

namespace AspisR1.SamplerBytePass

open Aeneas Aeneas.Std
open AspisR1.SamplerByteWord AspisR1.SamplerWordPass
open AspisR1.SamplerMachineBounds AspisR1.SamplerWord
open AspisR1.SamplerPass AspisV8R19.SamplerWordRead
open AspisV8R19.SqueezeOracleBridge AspisV8R19.SamplerWords

/-- The eight decoded little-endian words in the order consumed by the
high-to-low arithmetic pass. This definition records only the decoded source
digits; it does not assert an equivalence with a Rust sampler loop. -/
def digits (b : Array U8 32#usize) : List UInt32 :=
  (List.ofFn fun j : Fin 8 => UInt32.ofNat
    ((core.num.U32.from_le_bytes
      (four b (4 * j.val) (by omega))).val)).reverse

theorem digits_length (b : Array U8 32#usize) : (digits b).length = 8 := by
  simp [digits]

theorem digits_values (b : Array U8 32#usize) :
    (digits b).map UInt32.toNat =
      (List.ofFn fun j : Fin 8 =>
        AspisV8R19.SamplerWords.word
          (AspisV8R19.SqueezeOracleBridge.decodeState b) j).reverse := by
  simp only [digits, List.map_reverse, List.map_ofFn]
  apply congrArg List.reverse
  apply congrArg List.ofFn
  funext j
  exact AspisR1.SamplerByteWord.decodedArray_word_toNat b j

/-- The machine arithmetic pass on the eight decoded source words has the
same quotient and remainder equations as the general word-list theorem, with
the source words expressed as a reversed list of decoded Nat values. This is
not a theorem about the old sampler loop or `blockRank`. -/
theorem machineProcess_bytes_correct (r : UInt64) (b : Array U8 32#usize)
    (hr : r.toNat < P) :
    let output := machineProcess r (digits b)
    output.1.toNat =
        (r.toNat * B ^ 8 + numeral B
          ((List.ofFn fun j : Fin 8 =>
            AspisV8R19.SamplerWords.word
              (AspisV8R19.SqueezeOracleBridge.decodeState b) j).reverse)) % P ∧
      numeral B (output.2.map UInt32.toNat) =
        (r.toNat * B ^ 8 + numeral B
          ((List.ofFn fun j : Fin 8 =>
            AspisV8R19.SamplerWords.word
              (AspisV8R19.SqueezeOracleBridge.decodeState b) j).reverse)) / P := by
  simpa only [digits_length, digits_values] using
    (AspisR1.SamplerWordPass.machineProcess_correct r (digits b) hr)

#print axioms digits_values
#print axioms machineProcess_bytes_correct

end AspisR1.SamplerBytePass
