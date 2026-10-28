import JGg_QueryTotal
import NDO_JGg_Opening31
import Query31ConcreteWordsDriverChain
set_option autoImplicit false
namespace AspisR1.JGg_QueryWords1
open Aeneas Aeneas.Std Result
 def value : Array U32 8#usize := Array.make 8#usize [193093#u32,159813#u32,132355#u32,218094#u32,178080#u32,149624#u32,166165#u32,42158#u32]
theorem source : Query31ConcreteWordsDriverChain.actualQueryWords
    (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block1)=ok value := by
  obtain ⟨out,call⟩ := JGg_QueryTotal.words_total (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block1)
  have bytes := AspisR1QueryScanUnrolled.r0_transcript.query_words_success_byte_mask _ out call
  have numeric : (List.range 8).map (fun j => AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
      (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord
        (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block1) j))=value.val := by
    rfl
  have same : out=value := Subtype.ext (bytes.trans numeric)
  exact same ▸ call
#print axioms source
end AspisR1.JGg_QueryWords1
