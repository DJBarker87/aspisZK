import PAln_MatchingFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_MatchingInactive

theorem read (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (d : MatchingSupport.Data LiteralTranscript.E) (success : LiteralMatchingData.read rs=some d) :
    LiteralOpeningStages.readAt rs 28 (OpeningRecordCodec.decode .kappa)=some d.c0 := by
  obtain ⟨common,staged,row31,word,g,k,a0,a1,hc,hs,hr,hw,hg,hk,ha,hb,hd⟩ :=
    PAln_MatchingFacts.read_success_components rs d success
  rw [hd]
  change LiteralOpeningStages.readAt rs 28 (OpeningRecordCodec.decode .kappa)=some staged.toFirst.toKappa.row28
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
          rfl

#print axioms read
end AspisR1.F3M_MatchingInactive
end
