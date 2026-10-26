import F3P_ClaimsDecode
import F3P_ClaimsRecord
set_option autoImplicit false
namespace AspisR1.F3P_ClaimsMainRows
open Aeneas Aeneas.Std Result ClaimsUnrolledFinish

theorem source (std : StdCalls) (pre : MainPrefix) (out : MainClaims)
    (success : reference std pre=ok (.Ok out)) :
    ∃ (r : MainRecord) (a b c : Array MainQM 29#usize),
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize r 0#usize=ok (.Ok a) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize r 29#usize=ok (.Ok b) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize r 58#usize=ok (.Ok c) ∧
      out=Array.make 3#usize [a,b,c] := by
  obtain ⟨r,a,b,c,read,d0,d1,d2,same⟩ := F3P_ClaimsMain.reference std pre out success
  exact ⟨toMainRecord r,toMainArray a,toMainArray b,toMainArray c,
    F3P_ClaimsRecord.source pre r read,F3P_ClaimsDecode.decoded r 0#usize a d0,
    F3P_ClaimsDecode.decoded r 29#usize b d1,F3P_ClaimsDecode.decoded r 58#usize c d2,same⟩

#print axioms source
end AspisR1.F3P_ClaimsMainRows
