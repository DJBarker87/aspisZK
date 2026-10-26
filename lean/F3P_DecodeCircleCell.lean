import F3P_DecodeNumeric
import F3P_LowCellRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_DecodeCircleCell
open Aeneas Aeneas.Std Result

theorem cell {n : Usize} (r : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
    (offset : Usize) (out : Array AspisS1ExtractedRoundChildren.MainQM n)
    (success : AspisS1ExtractedRoundChildren.decodeMain n r offset=ok (.Ok out))
    (row : Fin 2) (values : CircleRecordCodec.Payload row)
    (decoded : CircleRecordCodec.decode row (MultiproofConeCanonical.bytesOf r.framed.val)=some values)
    (j : Fin n.val) (bound : offset.val+j.val<CircleRecordCodec.count row) :
    LiteralOpeningView.eK (F3L_RhoMeaning.decode
      (out.val[j.val]'(by simpa only [out.property] using j.isLt)))=
      (values ⟨offset.val+j.val,bound⟩).val := by
  have model := F3P_CircleCell.decoded row _ values decoded ⟨offset.val+j.val,bound⟩
  obtain ⟨value,source,numeric⟩ := F3P_DecodeNumeric.cell r offset out success j
  have low : SemanticCoefficientCodec.decodeLow
      (((((MultiproofConeCanonical.bytesOf r.framed.val).drop 5).drop (32*(offset.val+j.val))).take 32).take 16++
        List.replicate 16 0)=some value := by
    simpa only [List.drop_drop,List.take_take,show min 16 32=16 from rfl] using source
  have same := F3P_LowCellRead.identify _ _ _ model low
  exact numeric.symm.trans (congrArg Subtype.val same.symm)

#print axioms cell
end AspisR1.F3P_DecodeCircleCell
end
