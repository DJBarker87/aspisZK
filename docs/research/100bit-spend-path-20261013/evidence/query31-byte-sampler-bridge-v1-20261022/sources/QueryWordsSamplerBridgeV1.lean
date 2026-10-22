import QueryScanConcreteWordsDecoder
import R1SamplerByteWord
import AspisV8R19.SamplerWords
import AspisV8R19.SqueezeOracleBridge

open Aeneas Aeneas.Std
set_option autoImplicit false

namespace AspisR1QueryWordsSamplerBridgeV1

open AspisV8R19.SamplerWords
open AspisV8R19.SqueezeOracleBridge
open AspisR1QueryScanUnrolled.r0_transcript

/-- The source's 18-bit mask has the retained Q22 model value. -/
theorem query_mask_word_value (w : Std.U32) :
    (queryMaskWord w).val = AspisV8R19.SamplerWords.masked 18 w.val := by
  change (w.bv &&& (262143#u32).bv).toNat = _
  rw [BitVec.toNat_and]
  rfl

private def selectedFour (block : Array Std.U8 32#usize) (j : Fin 8) :
    Array Std.U8 4#usize := by
  have h32 : (32#usize : Usize).val = 32 := by scalar_tac
  refine ⟨[block.val[4*j.val]'(by rw [block.property, h32]; omega),
    block.val[4*j.val+1]'(by rw [block.property, h32]; omega),
    block.val[4*j.val+2]'(by rw [block.property, h32]; omega),
    block.val[4*j.val+3]'(by rw [block.property, h32]; omega)], ?_⟩
  simp

private theorem selectedFour_eq_window (block : Array Std.U8 32#usize)
    (j : Fin 8) :
    selectedFour block j = AspisV8R19.SamplerWordRead.four block (4*j.val) (by omega) := by
  apply Subtype.ext
  apply List.ext_getElem
  · have hleft : (selectedFour block j).val.length = 4 := by
      have h := (selectedFour block j).property
      have h4 : (4#usize : Usize).val = 4 := by scalar_tac
      simpa [h4] using h
    have hright : (AspisV8R19.SamplerWordRead.four block (4*j.val) (by omega)).val.length = 4 := by
      have h := (AspisV8R19.SamplerWordRead.four block (4*j.val) (by omega)).property
      have h4 : (4#usize : Usize).val = 4 := by scalar_tac
      simpa [h4] using h
    omega
  · intro i hi hj
    have hleft : (selectedFour block j).val.length = 4 := by
      have h := (selectedFour block j).property
      have h4 : (4#usize : Usize).val = 4 := by scalar_tac
      simpa [h4] using h
    have hright : (AspisV8R19.SamplerWordRead.four block (4*j.val) (by omega)).val.length = 4 := by
      have h := (AspisV8R19.SamplerWordRead.four block (4*j.val) (by omega)).property
      have h4 : (4#usize : Usize).val = 4 := by scalar_tac
      simpa [h4] using h
    have hi4 : i < 4 := by rw [hleft] at hi; exact hi
    interval_cases i <;> simp [selectedFour, AspisV8R19.SamplerWordRead.four,
      List.getElem_drop, List.getElem_take]

/-- One concrete extracted rank word is the little-endian word of the same
    exact 32-byte block after decoding it to the sampler's byte-state model. -/
theorem rank_word_value (block : Array Std.U8 32#usize)
    (j : Fin 8) :
    (blockRankWord block j.val).val =
      AspisV8R19.SamplerWords.word (AspisV8R19.SqueezeOracleBridge.decodeState block) j := by
  have hj : j.val < 8 := j.isLt
  unfold blockRankWord
  rw [dif_pos hj]
  change (core.num.U32.from_le_bytes (selectedFour block j)).val = _
  rw [selectedFour_eq_window]
  have hsource := AspisV8R19.SamplerWordBridge.source_word
    (AspisV8R19.SqueezeOracleBridge.decodeState block) j
  rw [AspisV8R19.SqueezeOracleBridge.array_roundtrip block] at hsource
  exact hsource

/-- A successful concrete `query_words` decode produces exactly the ordered
    list of eight 18-bit words consumed by the Q22 sampler model, on the same
    decoded byte block. -/
theorem query_words_success_sampler_words18
    (block : Array Std.U8 32#usize) (out : Array Std.U32 8#usize)
    (hdecode : AspisR1QueryScanUnrolled.r0_transcript.query_words block = .ok out) :
    out.val.map (fun w => w.val) = AspisV8R19.SamplerWords.words 18 (AspisV8R19.SqueezeOracleBridge.decodeState block) := by
  have hmask := query_words_success_byte_mask block out hdecode
  rw [hmask]
  unfold AspisV8R19.SamplerWords.words
  apply List.ext_getElem
  · simp
  · intro i hi _hj
    have hi8 : i < 8 := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [query_mask_word_value, rank_word_value block ⟨i, hi8⟩]

#print axioms query_mask_word_value
#print axioms rank_word_value
#print axioms query_words_success_sampler_words18

end AspisR1QueryWordsSamplerBridgeV1
