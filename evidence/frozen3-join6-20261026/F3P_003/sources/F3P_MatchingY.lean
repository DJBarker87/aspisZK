import PAln_MatchingFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_MatchingY

theorem read (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (d : MatchingSupport.Data LiteralTranscript.E) (success : LiteralMatchingData.read rs=some d) :
    ∃ (r25 : CircleRecordCodec.Payload 0) (r26 : CircleRecordCodec.Payload 1)
      (r27 : OpeningRecordCodec.Payload .gamma),
      LiteralOpeningStages.readAt rs 25 (CircleRecordCodec.decode 0)=some r25 ∧
      LiteralOpeningStages.readAt rs 26 (CircleRecordCodec.decode 1)=some r26 ∧
      LiteralOpeningStages.readAt rs 27 (OpeningRecordCodec.decode .gamma)=some r27 ∧
      d.Y=SelectedOpeningClaims.Y r25 r26 r27 := by
  obtain ⟨common,staged,row31,word,g,k,a0,a1,hc,hs,hr,hw,hg,hk,ha,hb,hd⟩ :=
    PAln_MatchingFacts.read_success_components rs d success
  unfold LiteralOpeningStages.readSecond LiteralOpeningStages.readFirst LiteralOpeningStages.readKappa at hs
  cases hgamma : LiteralOpeningStages.readGamma rs with
  | none => simp [hgamma] at hs
  | some gamma =>
    cases h28 : LiteralOpeningStages.readAt rs 28 (OpeningRecordCodec.decode .kappa) with
    | none => simp [hgamma,h28] at hs
    | some value =>
      cases h29 : LiteralOpeningStages.readAt rs 29 (OpeningRecordCodec.decode .first) with
      | none => simp [hgamma,h28,h29] at hs
      | some first =>
        cases h30 : LiteralOpeningStages.readAt rs 30 (OpeningRecordCodec.decode .second) with
        | none => simp [hgamma,h28,h29,h30] at hs
        | some second =>
          simp [hgamma,h28,h29,h30] at hs
          subst staged
          unfold LiteralOpeningStages.readGamma at hgamma
          cases h25 : LiteralOpeningStages.readAt rs 25 (CircleRecordCodec.decode 0) with
          | none => simp [h25] at hgamma
          | some r25 =>
            cases h26 : LiteralOpeningStages.readAt rs 26 (CircleRecordCodec.decode 1) with
            | none => simp [h25,h26] at hgamma
            | some r26 =>
              cases h27 : LiteralOpeningStages.readAt rs 27 (OpeningRecordCodec.decode .gamma) with
              | none => simp [h25,h26,h27] at hgamma
              | some r27 =>
                simp [h25,h26,h27] at hgamma
                subst gamma
                exact ⟨r25,r26,r27,rfl,rfl,rfl,by rw [hd];rfl⟩

#print axioms read
end AspisR1.F3P_MatchingY
end
