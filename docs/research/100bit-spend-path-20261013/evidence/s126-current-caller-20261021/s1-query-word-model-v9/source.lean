import S1QueryByteChainV1
import Query31ConcreteWordsDriverChain
import AspisV8R19.SamplerWords
set_option autoImplicit false
namespace AspisS1QueryWordModel
open Aeneas Aeneas.Std Result
open AspisR1QueryScanUnrolled.r0_transcript
open AspisV8R19.SqueezeOracleBridge

/-- Literal four-byte LE conversion, without arithmetic success premises. -/
theorem le_word_value (a b c d : U8) :
    (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).val=
      a.val+256*b.val+65536*c.val+16777216*d.val := by
  have pack : BitVec.fromLEBytes [a.bv,b.bv,c.bv,d.bv]=d.bv++c.bv++b.bv++a.bv := by
    simp only [BitVec.fromLEBytes,List.length_cons,List.length_nil]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_or,BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft,BitVec.getLsbD_append,BitVec.getLsbD_zero]
    have h1 : i-8<32 := by omega
    have h2 : i-8<24 := by omega
    have h3 : i-8-8<24 := by omega
    have h4 : i-8-8<16 := by omega
    have h5 : i-8-8-8<16 := by omega
    have h6 : i-8-8-8<8 := by omega
    split_ifs <;> simp_all
    all_goals
      have hn0 : ¬i<8 := by omega
      have hn1 : ¬i-8<8 := by omega
      simp only [hn0,hn1,decide_false,Bool.not_false,Bool.true_and]
    have hn2 : ¬i-8-8<8 := by omega
    simp [hn2]
  change (BitVec.fromLEBytes [a.bv,b.bv,c.bv,d.bv]).toNat=_
  rw [pack]
  simp only [BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt a.bv.isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt b.bv.isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt c.bv.isLt]
  simp only [Nat.shiftLeft_eq]
  change ((d.val*256+c.val)*256+b.val)*256+a.val=_
  omega

/-- The source's exact byte offsets agree with the fixed sampler word. -/
theorem block_word_value (block : Array U8 32#usize) (j : Fin 8) :
    (blockRankWord block j.val).val=AspisV8R19.SamplerWords.word (decodeState block) j := by
  rw [blockRankWord,dif_pos j.isLt]
  exact le_word_value _ _ _ _

theorem masked_word_value (block : Array U8 32#usize) (j : Fin 8) :
    (queryMaskWord (blockRankWord block j.val)).val=
      AspisV8R19.SamplerWords.masked 18 (AspisV8R19.SamplerWords.word (decodeState block) j) := by
  change ((blockRankWord block j.val).bv &&& (262143#u32).bv).toNat=_
  rw [BitVec.toNat_and]
  change (blockRankWord block j.val).val &&& 262143=_
  rw [block_word_value]
  rfl

/-- ACCEPTED-ONLY word decoding equality for the existing source-shaped
from_fn/map decoder; no native iterator or allocator correspondence is inferred. -/
theorem query_words_math (block : Array U8 32#usize) (out : Array U32 8#usize)
    (success : query_words block=ok out) :
    out.val.map (fun w => w.val)=AspisV8R19.SamplerWords.words 18 (decodeState block) := by
  rw [query_words_success_byte_mask block out success,List.map_map]
  apply List.ext_getElem
  · simp [AspisV8R19.SamplerWords.words]
  · intro i hi hj
    have hi8 : i<8 := by simpa using hi
    simpa only [AspisV8R19.SamplerWords.words,List.getElem_ofFn,List.getElem_map,
      List.getElem_range,Function.comp_apply] using masked_word_value block ⟨i,hi8⟩

#print axioms le_word_value
#print axioms block_word_value
#print axioms masked_word_value
#print axioms query_words_math
end AspisS1QueryWordModel
