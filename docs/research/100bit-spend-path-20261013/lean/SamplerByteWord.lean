import AspisV8R19.SamplerWordBridge

set_option autoImplicit false

namespace AspisR1.SamplerByteWord

open Aeneas Aeneas.Std AspisV8R19.SamplerWordRead
open AspisV8R19.SqueezeOracleBridge AspisV8R19.SamplerWords
open AspisV8R19.SamplerWordBridge

/-- Adapt one decoded four-byte source word to the corresponding Lean UInt32
digit. This is only the byte decoding bridge; it says nothing about sampler
loop order or rejection behavior. -/
theorem decodedArray_word_toNat (b : Array U8 32#usize) (j : Fin 8) :
    (UInt32.ofNat ((core.num.U32.from_le_bytes
      (four b (4 * j.val) (by omega))).val)).toNat =
      AspisV8R19.SamplerWords.word
        (AspisV8R19.SqueezeOracleBridge.decodeState b) j := by
  have hsource := AspisV8R19.SamplerWordBridge.source_word
    (AspisV8R19.SqueezeOracleBridge.decodeState b) j
  rw [AspisV8R19.SqueezeOracleBridge.array_roundtrip b] at hsource
  rw [hsource, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (AspisV8R19.SamplerWords.word_bound _ _)

#print axioms decodedArray_word_toNat

end AspisR1.SamplerByteWord
