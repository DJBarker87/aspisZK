import FJq_ParentRows
import FJq_SourceDecode
import FJq_SourceRecord
import FJq_ClaimsRoundtrip
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ReferenceMain
open Aeneas Aeneas.Std Result ClaimsUnrolledFinish
/-- All original main claim rows and row25 provenance, derived from one
installed Claims reference call with its actual operational dictionary. -/
theorem reached (std : StdCalls) (pre : MainPrefix) (out : MainClaims)
    (run : reference std pre=ok (.Ok out)) :
    ∃ (record : MainRecord) (a b c : Array MainQM 29#usize),
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok record) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize record 0#usize=ok (.Ok a) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize record 29#usize=ok (.Ok b) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize record 58#usize=ok (.Ok c) ∧
      out=(⟨[a,b,c],by simp⟩ : MainClaims) := by
  unfold reference at run
  cases called : AspisR1ClaimsUnrolledParent.claimsReference (external std) (fromMainPrefix pre) with
  | fail e=>rw [called] at run;cases run
  | div=>rw [called] at run;cases run
  | ok status=>
    rw [called] at run
    cases status with
    | Err e=>cases run
    | Ok parent=>
      have output : (⟨parent.val.map toMainArray,by simpa using parent.property⟩ : MainClaims)=out :=
        core.result.Result.Ok.inj (Result.ok.inj run)
      obtain ⟨record,read,decoded⟩:=FJq_ReferenceRecord.reached (external std) _ parent called
      obtain ⟨a,b,c,ha,hb,hc,shape⟩:=FJq_ParentRows.reached (external std) record parent decoded
      obtain ⟨ma,hma,ea⟩:=FJq_SourceDecode.reached 29#usize record 0#usize a ha
      obtain ⟨mb,hmb,eb⟩:=FJq_SourceDecode.reached 29#usize record 29#usize b hb
      obtain ⟨mc,hmc,ec⟩:=FJq_SourceDecode.reached 29#usize record 58#usize c hc
      refine ⟨toMainRecord record,ma,mb,mc,FJq_SourceRecord.reached _ 25#u8 record read,hma,hmb,hmc,?_⟩
      rw [←output,shape,ea,eb,ec]
      apply Subtype.ext
      simp only [List.map_cons,List.map_nil,FJq_ClaimsRoundtrip.row]
#print axioms reached
end AspisR1.FJq_ReferenceMain
end
