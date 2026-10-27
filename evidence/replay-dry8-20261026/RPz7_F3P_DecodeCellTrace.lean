import RPz7_F3P_DecodeCells
import F3P_Offset
set_option autoImplicit false
namespace AspisR1.F3P_DecodeCellTrace
open Aeneas Aeneas.Std Result

theorem source {n : Usize} (r : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
    (offset : Usize) (out : Array AspisS1ExtractedRoundChildren.MainQM n)
    (success : AspisS1ExtractedRoundChildren.decodeMain n r offset=ok (.Ok out))
    (j : Fin n.val) :
    ∃ (byteOffset : Usize) (q : AspisS1ExtractedRoundChildren.DecodeQM),
      byteOffset.val=32*offset.val ∧
      out.val[j.val]'(by simpa only [out.property] using j.isLt)=AspisS1ExtractedRoundChildren.decoderQMToMain q ∧
      Nonempty (AspisR1DecodeKFullValueTrace.ParserTrace
        (AspisS1ExtractedRoundChildren.recordToDecoder r) byteOffset
        (UScalar.ofNatCore j.val (by have := j.isLt;scalar_tac)) offset q) := by
  obtain ⟨decoded,ran,same⟩ := F3P_DecodeCells.source r offset out success
  obtain ⟨byteOffset,mult,read⟩ := AspisR1DecodeKFullSuccessIndexedParser.decode_k_success_indexed_parser
    n (AspisS1ExtractedRoundChildren.recordToDecoder r) offset decoded ran
  obtain ⟨q,called,cell,trace⟩ := read j j.isLt
  refine ⟨byteOffset,q,F3P_Offset.value offset byteOffset mult,?_,trace⟩
  rw [← same]
  simp only [AspisS1ExtractedRoundChildren.decoderArrayToMain,List.getElem_map,cell]

#print axioms source
end AspisR1.F3P_DecodeCellTrace
