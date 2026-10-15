import R1LiteralOpeningBinding
import R1LiteralIndexedPrefix
import R1LiteralClassifier
import R1GenericNoHitIndex

/-! The literal no-hit classifier supplies the four exclusions needed by the
existing opening binding theorem once the terminal data reader succeeds.
Gamma nonzero is a separate explicit premise here, supplied by the sampler
rather than by bad-set exclusion. Acceptance and source correspondence are
not assumed or claimed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralOpeningGood

open LiteralTranscript LiteralIndexedPrefix
abbrev E := LiteralTranscript.E

-- The proof only transports membership in these symbolic sets.
attribute [local irreducible] ConcreteBinding.gammaBad ConcreteBinding.kappaBad
  ConcreteBinding.firstBad ConcreteBinding.secondBad
  LiteralOpeningEvents.gammaBad LiteralOpeningEvents.kappaBad
  LiteralOpeningEvents.firstBad LiteralOpeningEvents.secondBad

theorem good_of_read_noHit (pub : Public)
    (rs : List (Message × Challenge)) (d : MatchingSupport.Data E)
    (hlen : 32 ≤ rs.length)
    (hread : LiteralMatchingData.read rs = some d)
    (hnonzero : d.gamma ≠ 0)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub [] rs) :
    MatchingSupport.Good d := by
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hc, hs, hr31, hw, hg, hk, ha0, ha1, hd⟩ :=
    LiteralMatchingFacts.read_success_components rs d hread
  have h27 := (LiteralReadAtFacts.readGamma_current rs staged.toGamma
    (LiteralStageFacts.readSecond_gamma rs staged hs)).2.2
  have h28 := LiteralReadAtFacts.readKappa_current rs staged.toKappa
    (LiteralStageFacts.readSecond_kappa rs staged hs)
  have h29 := LiteralReadAtFacts.readFirst_current rs staged.toFirst
    (LiteralStageFacts.readSecond_first rs staged hs)
  have h30 := LiteralReadAtFacts.readSecond_current rs staged hs
  have hi27 : 27 < rs.length := by omega
  have hv27 := readAt_success_index_valid rs 27 hi27 _ _ h27
  have hc27 : LiteralChallengeRead.ordinaryAt rs 27 = some d.gamma := by
    rw [hd]
    exact hg
  have hx27 := ordinaryAt_success_index_value rs 27 hi27 d.gamma hc27
  have hn27 := GenericNoHitIndex.not_bad_at_index
    LiteralClassifier.bad pub rs 27 hi27 hno
  have hr27 := take_prefix_round pub rs 27 hi27
  have he27 := full_take_index_drop pub rs 27 hi27
  have hb27 := LiteralOpeningBinding.gamma_bad_iff
    ⟨pub, rs.take 27⟩ rs[27].1 rs[27].2 (rs.drop (27+1)) d hr27
    (by rw [he27]; exact hread) d.gamma
  have hngamma : d.gamma ∉ ConcreteBinding.gammaBad d.W d.F d.Y := by
    intro hbad
    apply hn27
    have hactual := hb27.mpr hbad
    simpa only [LiteralClassifier.bad, hr27, LiteralOrdinaryDensity.event,
      hx27, hv27, true_and, Nat.reduceLT, if_false] using hactual
  have hi28 : 28 < rs.length := by omega
  have hv28 := readAt_success_index_valid rs 28 hi28 _ _ h28
  have hc28 : LiteralChallengeRead.ordinaryAt rs 28 = some d.kappa := by
    rw [hd]
    exact hk
  have hx28 := ordinaryAt_success_index_value rs 28 hi28 d.kappa hc28
  have hn28 := GenericNoHitIndex.not_bad_at_index
    LiteralClassifier.bad pub rs 28 hi28 hno
  have hr28 := take_prefix_round pub rs 28 hi28
  have he28 := full_take_index_drop pub rs 28 hi28
  have hb28 := LiteralOpeningBinding.kappa_bad_iff
    ⟨pub, rs.take 28⟩ rs[28].1 rs[28].2 (rs.drop (28+1)) d hr28
    (by rw [he28]; exact hread) d.kappa
  have hnkappa : d.kappa ∉ ConcreteBinding.kappaBad d.W d.F d.F0 d.Y d.c0 d.gamma := by
    intro hbad
    apply hn28
    have hactual := hb28.mpr hbad
    simpa only [LiteralClassifier.bad, hr28, LiteralOrdinaryDensity.event,
      hx28, hv28, true_and, Nat.reduceLT, if_false] using hactual
  have hi29 : 29 < rs.length := by omega
  have hv29 := readAt_success_index_valid rs 29 hi29 _ _ h29
  have hc29 : LiteralChallengeRead.ordinaryAt rs 29 = some d.alpha0 := by
    rw [hd]
    exact ha0
  have hx29 := ordinaryAt_success_index_value rs 29 hi29 d.alpha0 hc29
  have hn29 := GenericNoHitIndex.not_bad_at_index
    LiteralClassifier.bad pub rs 29 hi29 hno
  have hr29 := take_prefix_round pub rs 29 hi29
  have he29 := full_take_index_drop pub rs 29 hi29
  have hb29 := LiteralOpeningBinding.first_bad_iff
    ⟨pub, rs.take 29⟩ rs[29].1 rs[29].2 (rs.drop (29+1)) d hr29
    (by rw [he29]; exact hread) d.alpha0
  have hnfirst : d.alpha0 ∉ ConcreteBinding.firstBad d.W d.gamma (FunctionalWeights.weights d.F d.F0 d.kappa) d.p0 := by
    intro hbad
    apply hn29
    have hactual := hb29.mpr hbad
    simpa only [LiteralClassifier.bad, hr29, LiteralOrdinaryDensity.event,
      hx29, hv29, true_and, Nat.reduceLT, if_false] using hactual
  have hi30 : 30 < rs.length := by omega
  have hv30 := readAt_success_index_valid rs 30 hi30 _ _ h30
  have hc30 : LiteralChallengeRead.ordinaryAt rs 30 = some d.alpha1 := by
    rw [hd]
    exact ha1
  have hx30 := ordinaryAt_success_index_value rs 30 hi30 d.alpha1 hc30
  have hn30 := GenericNoHitIndex.not_bad_at_index
    LiteralClassifier.bad pub rs 30 hi30 hno
  have hr30 := take_prefix_round pub rs 30 hi30
  have he30 := full_take_index_drop pub rs 30 hi30
  have hb30 := LiteralOpeningBinding.second_bad_iff
    ⟨pub, rs.take 30⟩ rs[30].1 rs[30].2 (rs.drop (30+1)) d hr30
    (by rw [he30]; exact hread) d.alpha1
  have hnsecond : d.alpha1 ∉ ConcreteBinding.secondBad d.W d.V d.gamma d.alpha0 (FunctionalWeights.weights d.F d.F0 d.kappa) d.p1 := by
    intro hbad
    apply hn30
    have hactual := hb30.mpr hbad
    simpa only [LiteralClassifier.bad, hr30, LiteralOrdinaryDensity.event,
      hx30, hv30, true_and, Nat.reduceLT, if_false] using hactual
  exact ⟨hnonzero, hngamma, hnkappa, hnfirst, hnsecond⟩

#print axioms good_of_read_noHit

end AspisR1.LiteralOpeningGood
end
