import JGg_QueryTotal
import NDO_JGg_Opening31
import Query31ConcreteWordsDriverChain
set_option autoImplicit false
namespace AspisR1.JGg_QueryWords0
open Aeneas Aeneas.Std Result
 def value : Array U32 8#usize := Array.make 8#usize [93499#u32,147529#u32,216823#u32,245899#u32,209371#u32,192317#u32,65593#u32,183859#u32]
theorem source : Query31ConcreteWordsDriverChain.actualQueryWords
    (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block0)=ok value := by
  obtain ⟨out,call⟩ := JGg_QueryTotal.words_total (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block0)
  have bytes := AspisR1QueryScanUnrolled.r0_transcript.query_words_success_byte_mask _ out call
  have numeric : (List.range 8).map (fun j => AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
      (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord
        (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block0) j))=value.val := by
    rfl
  have same : out=value := Subtype.ext (bytes.trans numeric)
  exact same ▸ call
#print axioms source
end AspisR1.JGg_QueryWords0
