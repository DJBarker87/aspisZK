import JGg_QueryTotal
import NDO_JGg_Opening31
import Query31ConcreteWordsDriverChain
set_option autoImplicit false
namespace AspisR1.JGg_QueryWords2
open Aeneas Aeneas.Std Result
 def value : Array U32 8#usize := Array.make 8#usize [179622#u32,21248#u32,63860#u32,55377#u32,185637#u32,14297#u32,26524#u32,99234#u32]
theorem source : Query31ConcreteWordsDriverChain.actualQueryWords
    (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block2)=ok value := by
  obtain ⟨out,call⟩ := JGg_QueryTotal.words_total (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block2)
  have bytes := AspisR1QueryScanUnrolled.r0_transcript.query_words_success_byte_mask _ out call
  have numeric : (List.range 8).map (fun j => AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
      (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord
        (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block2) j))=value.val := by
    rfl
  have same : out=value := Subtype.ext (bytes.trans numeric)
  exact same ▸ call
#print axioms source
end AspisR1.JGg_QueryWords2
