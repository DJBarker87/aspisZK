import RPu_FJq_LiteralGamma
import R1LiteralMatchingData
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_LiteralY
/-- The matching reader's actual Y is exactly its decoded row25/26/27 payloads. -/
theorem reached (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (out : MatchingSupport.Data AspisWideTower.WideExact)
    (run : LiteralMatchingData.read rs=some out) :
    ∃ (a : CircleRecordCodec.Payload 0) (b : CircleRecordCodec.Payload 1)
      (c : OpeningRecordCodec.Payload .gamma),
      LiteralOpeningStages.readAt rs 25 (CircleRecordCodec.decode 0)=some a ∧
      LiteralOpeningStages.readAt rs 26 (CircleRecordCodec.decode 1)=some b ∧
      LiteralOpeningStages.readAt rs 27 (OpeningRecordCodec.decode .gamma)=some c ∧
      out.Y=SelectedOpeningClaims.Y a b c := by
  unfold LiteralMatchingData.read at run
  obtain ⟨common,hcommon,run⟩:=Option.bind_eq_some_iff.mp run
  obtain ⟨staged,hstaged,run⟩:=Option.bind_eq_some_iff.mp run
  obtain ⟨row31,h31,run⟩:=Option.bind_eq_some_iff.mp run
  obtain ⟨word,hw,run⟩:=Option.bind_eq_some_iff.mp run
  obtain ⟨gamma,hg,run⟩:=Option.bind_eq_some_iff.mp run
  obtain ⟨kappa,hk,run⟩:=Option.bind_eq_some_iff.mp run
  obtain ⟨alpha0,ha0,run⟩:=Option.bind_eq_some_iff.mp run
  obtain ⟨alpha1,ha1,run⟩:=Option.bind_eq_some_iff.mp run
  have same:=Option.some.inj run
  subst out
  have rows:=FJq_LiteralGamma.reached rs _ (FJq_LiteralStages.reached rs staged hstaged)
  exact ⟨_,_,_,rows.1,rows.2.1,rows.2.2,rfl⟩
#print axioms reached
end AspisR1.FJq_LiteralY
end
