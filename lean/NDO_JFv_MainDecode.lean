import NDO_JFv_ClaimsRecord
set_option autoImplicit false
namespace AspisR1.JFv_MainDecode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open OraclePortCompactDraft MultiproofConeCanonical

theorem success (N : Usize) (vr : r1_wire.ValidatedRecord) (offset : Usize)
    (row : 14 ≤ vr.row.val) (bound : 5+32*(offset.val+N.val) ≤ vr.framed.length)
    (small : vr.framed.length ≤ 20000)
    (canon : canonical (bytesOf (vr.framed.val.drop 5))) :
    ∃ out,AspisS1ExtractedRoundChildren.decodeMain N vr offset=ok (.Ok out) := by
  obtain ⟨out,call⟩ := JFv_Decode.success N (AspisS1ExtractedRoundChildren.recordToDecoder vr)
    offset row bound small canon
  refine ⟨AspisS1ExtractedRoundChildren.decoderArrayToMain out,?_⟩
  unfold AspisS1ExtractedRoundChildren.decodeMain
  rw [call]
  rfl

#print axioms success
end AspisR1.JFv_MainDecode
