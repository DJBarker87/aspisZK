import NBL_InitTrace
set_option autoImplicit false
namespace AspisR1.NBL_ByteWord
open Aeneas Aeneas.Std

/-- The per-write native byte polynomial is the SAME word used by the
high-to-low division input; both reversals and the exact position are exposed. -/
theorem source (block : Array U8 32#usize) (i : Fin 8) :
    (NBL_InitTrace.byteWord block i).toNat=
      AspisV8R19.SamplerWords.word (AspisV8R19.SqueezeOracleBridge.decodeState block) i := by
  simp only [NBL_InitTrace.byteWord,SamplerBytePass.digits,List.reverse_reverse,List.getElem_ofFn]
  exact SamplerByteWord.decodedArray_word_toNat block i

#print axioms source
end AspisR1.NBL_ByteWord
