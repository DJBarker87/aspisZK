import F3P_DecodeCellTrace
import F3P_TracePayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_DecodeNumeric
open Aeneas Aeneas.Std Result

theorem cell {n : Usize} (r : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
    (offset : Usize) (out : Array AspisS1ExtractedRoundChildren.MainQM n)
    (success : AspisS1ExtractedRoundChildren.decodeMain n r offset=ok (.Ok out))
    (j : Fin n.val) :
    ∃ value : SemanticCoefficientCodec.LowWide,
      SemanticCoefficientCodec.decodeLow
        (((MultiproofConeCanonical.bytesOf r.framed.val).drop (5+32*(offset.val+j.val))).take 16++
          List.replicate 16 0)=some value ∧
      value.val=LiteralOpeningView.eK (F3L_RhoMeaning.decode
        (out.val[j.val]'(by simpa only [out.property] using j.isLt))) := by
  obtain ⟨byteOffset,q,offsetEq,cellEq,⟨trace⟩⟩ := F3P_DecodeCellTrace.source r offset out success j
  obtain ⟨value,decoded,numeric⟩ := F3P_TraceParsed.parsed _ _ _ _ _ trace
  rw [F3P_TracePayload.bytes] at decoded
  simp only [MultiproofConeCanonical.bytesOf,List.map_take,List.map_drop,List.drop_drop] at decoded
  rw [offsetEq] at decoded
  have position : 5+(32*offset.val+32*(UScalar.ofNatCore j.val (by have := j.isLt;scalar_tac) : Usize).val)=
      5+32*(offset.val+j.val) := by simp only [UScalar.val_ofNatCore];omega
  rw [position] at decoded
  refine ⟨value,?_,?_⟩
  · simpa only [MultiproofConeCanonical.bytesOf,List.map_take,List.map_drop] using decoded
  · rw [cellEq]
    exact numeric

#print axioms cell
end AspisR1.F3P_DecodeNumeric
end
