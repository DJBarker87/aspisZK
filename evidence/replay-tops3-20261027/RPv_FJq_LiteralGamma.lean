import RPv_FJq_LiteralStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_LiteralGamma
/-- Complete literal payload reads retained with their original row numbers. -/
theorem reached (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (out : LiteralOpeningStages.Gamma) (run : LiteralOpeningStages.readGamma rs=some out) :
    LiteralOpeningStages.readAt rs 25 (CircleRecordCodec.decode 0)=some out.row25 ∧
    LiteralOpeningStages.readAt rs 26 (CircleRecordCodec.decode 1)=some out.row26 ∧
    LiteralOpeningStages.readAt rs 27 (OpeningRecordCodec.decode .gamma)=some out.row27 := by
  unfold LiteralOpeningStages.readGamma at run
  obtain ⟨row25,h25,run⟩:=Option.bind_eq_some_iff.mp run
  obtain ⟨row26,h26,run⟩:=Option.bind_eq_some_iff.mp run
  obtain ⟨row27,h27,run⟩:=Option.bind_eq_some_iff.mp run
  have same:=Option.some.inj run
  subst out
  exact ⟨h25,h26,h27⟩
#print axioms reached
end AspisR1.FJq_LiteralGamma
end
