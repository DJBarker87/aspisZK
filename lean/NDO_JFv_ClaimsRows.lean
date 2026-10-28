import NDO_JFv_MainDecode
set_option autoImplicit false
namespace AspisR1.JFv_ClaimsRows
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem success (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) :
    ∃ vr r0 r1 r2,r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok vr) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize vr 0#usize=ok (.Ok r0) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize vr 29#usize=ok (.Ok r1) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize vr 58#usize=ok (.Ok r2) := by
  obtain ⟨vr,call,row,length,canon⟩ := JFv_ClaimsRecord.fields bytes pre parsed
  have large : 14 ≤ vr.row.val := by rw [row];decide
  have small : vr.framed.length ≤ 20000 := by change vr.framed.val.length ≤ 20000;rw [length];decide
  obtain ⟨r0,h0⟩ := JFv_MainDecode.success 29#usize vr 0#usize large
    (by change 5+32*(0+29) ≤ vr.framed.val.length;rw [length];decide) small canon
  obtain ⟨r1,h1⟩ := JFv_MainDecode.success 29#usize vr 29#usize large
    (by change 5+32*(29+29) ≤ vr.framed.val.length;rw [length];decide) small canon
  obtain ⟨r2,h2⟩ := JFv_MainDecode.success 29#usize vr 58#usize large
    (by change 5+32*(58+29) ≤ vr.framed.val.length;rw [length];decide) small canon
  exact ⟨vr,r0,r1,r2,call,h0,h1,h2⟩

#print axioms success
end AspisR1.JFv_ClaimsRows
