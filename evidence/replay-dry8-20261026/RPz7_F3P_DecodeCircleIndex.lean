import RPz7_F3P_ArrayIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_DecodeCircleIndex
open Aeneas Aeneas.Std Result

theorem cell {n : Usize} (r : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
    (offset : Usize) (out : Array AspisS1ExtractedRoundChildren.MainQM n)
    (success : AspisS1ExtractedRoundChildren.decodeMain n r offset=ok (.Ok out))
    (row : Fin 2) (values : CircleRecordCodec.Payload row)
    (decoded : CircleRecordCodec.decode row (MultiproofConeCanonical.bytesOf r.framed.val)=some values)
    (l : Usize) (hl : l.val<n.val) (bound : offset.val+l.val<CircleRecordCodec.count row)
    (scalar : AspisS1ExtractedRoundChildren.MainQM) (read : Array.index_usize out l=ok scalar) :
    LiteralOpeningView.eK (F3L_RhoMeaning.decode scalar)=(values ⟨offset.val+l.val,bound⟩).val := by
  obtain ⟨length,same⟩ := F3P_ArrayIndex.cell out l scalar read
  have numeric := F3P_DecodeCircleCell.cell r offset out success row values decoded ⟨l.val,hl⟩ bound
  rw [same] at numeric
  exact numeric

#print axioms cell
end AspisR1.F3P_DecodeCircleIndex
end
