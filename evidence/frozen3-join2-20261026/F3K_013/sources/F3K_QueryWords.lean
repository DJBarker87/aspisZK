import F3K_QueryDecoderSource
import Query31ConcreteMaterializedSchedule
import AspisV8R19.SamplerWordBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryWords
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge AspisV8R19.SourceDuplexStep
open AspisR1QueryScanUnrolled.r0_transcript

theorem word (b : Array U8 32#usize) (j : Fin 8) :
    (blockRankWord b j.val).val=AspisV8R19.SamplerWords.word (decodeState b) j := by
  rw [blockRankWord,dif_pos j.isLt]
  change (core.num.U32.from_le_bytes (Array.make 4#usize
    [b.val[4*j.val]'(by have h:=b.property;omega),
     b.val[4*j.val+1]'(by have h:=b.property;omega),
     b.val[4*j.val+2]'(by have h:=b.property;omega),
     b.val[4*j.val+3]'(by have h:=b.property;omega)])).val=_
  rw [AspisV8R19.SamplerWordBridge.four_bytes]
  rfl

theorem mask (w : U32) :
    (queryMaskWord w).val=AspisV8R19.SamplerWords.masked 18 w.val := by
  change (w.bv &&& (262143#u32).bv).toNat=_
  rw [BitVec.toNat_and]
  rfl

theorem decoded (b : Array U8 32#usize) (ws : Array U32 8#usize)
    (h : Query31ConcreteWordsDriverChain.actualQueryWords b=ok ws) :
    ws.val.map (fun x => x.val)=AspisV8R19.SamplerWords.words 18 (decodeState b) := by
  have shape := query_words_success_byte_mask b ws h
  rw [shape,List.map_map]
  unfold AspisV8R19.SamplerWords.words
  rw [List.ofFn_eq_map]
  apply List.map_congr_left
  intro j hj
  rw [mask,word b ⟨j,List.mem_range.mp hj⟩]

#print axioms word
#print axioms mask
#print axioms decoded
end AspisR1.F3K_QueryWords
end
