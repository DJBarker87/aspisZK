import PAln_MatchingFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_MatchingChallenges

theorem fields (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (d : MatchingSupport.Data LiteralTranscript.E)
    (read : LiteralMatchingData.read rs=some d) :
    LiteralChallengeRead.ordinaryAt rs 27=some d.gamma ∧
    LiteralChallengeRead.ordinaryAt rs 28=some d.kappa ∧
    LiteralChallengeRead.ordinaryAt rs 29=some d.alpha0 ∧
    LiteralChallengeRead.ordinaryAt rs 30=some d.alpha1 := by
  obtain ⟨common,staged,row31,word,g,k,a,b,_,_,_,_,hg,hk,ha,hb,same⟩ :=
    PAln_MatchingFacts.read_success_components rs d read
  subst d
  exact ⟨hg,hk,ha,hb⟩

#print axioms fields
end AspisR1.F3L_MatchingChallenges
end
