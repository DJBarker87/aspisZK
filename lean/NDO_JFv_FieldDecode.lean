import NDO_JFv_FieldRecord
import NDO_JFv_MainDecode
set_option autoImplicit false
namespace AspisR1.JFv_FieldDecode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft

theorem success (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) (row : U8)
    (valid : row.val<27) (field : 14 ≤ row.val) (N offset : Usize)
    (fits : 32*(offset.val+N.val) ≤ (rowShape row.val).2) :
    ∃ vr out,r1_wire.Prefix.validated_record pre row=ok (.Ok vr) ∧
      AspisS1ExtractedRoundChildren.decodeMain N vr offset=ok (.Ok out) := by
  obtain ⟨vr,call,same,length,canon⟩ := JFv_FieldRecord.fields bytes pre parsed row valid field
  have small := (JFw_Geometry.step row.val valid).1
  obtain ⟨out,decoded⟩ := JFv_MainDecode.success N vr offset (by rw [same];exact field)
    (by change 5+32*(offset.val+N.val) ≤ vr.framed.val.length;omega)
    (by change vr.framed.val.length ≤ 20000;omega) canon
  exact ⟨vr,out,call,decoded⟩

#print axioms success
end AspisR1.JFv_FieldDecode
