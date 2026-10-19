import AspisFormal.V5FriDegreeThreeCorrelatedAgreement

/-! Matched-response form of degree-three curve decodability. The support
masking and root-union argument are the degree-three analogue of
`width29_bad_response_challenges_card_le`. Challenges include zero. -/
set_option autoImplicit false
namespace AspisWide.DegreeThreeMatched
open AspisV5FriDegreeThreeCorrelatedAgreement

variable {K Domain Message : Type*}
  [Field K] [Fintype K] [DecidableEq K]
  [Fintype Domain] [DecidableEq Domain]

def HasMatchingDecomposition
    (encoder : Message → Domain → K) (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) (z : K) : Prop :=
  ∃ components : Fin 4 → Message,
    strategy.support z ⊆ jointAgreementSet encoder lanes components ∧
    CandidateOnCurve encoder strategy components z

def BadResponse
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) (z : K) : Prop :=
  ValidResponse encoder agreementThreshold lanes strategy z ∧
    ¬ HasMatchingDecomposition encoder lanes strategy z

noncomputable def badStrategy
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) :
    ProximateStrategy K Domain Message := by
  classical
  exact {
    candidate := strategy.candidate
    support := fun z =>
      if BadResponse encoder agreementThreshold lanes strategy z
      then strategy.support z else ∅
  }

theorem mem_badStrategy_good_iff
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) (z : K) :
    z ∈ goodChallenges encoder agreementThreshold lanes
        (badStrategy encoder agreementThreshold lanes strategy) ↔
      BadResponse encoder agreementThreshold lanes strategy z := by
  classical
  rw [mem_goodChallenges_iff]
  constructor
  · intro h
    by_cases hbad : BadResponse encoder agreementThreshold lanes strategy z
    · exact hbad
    · have hempty :
          (badStrategy encoder agreementThreshold lanes strategy).support z = ∅ := by
        simp [badStrategy, hbad]
      have himpossible : agreementThreshold < 0 := by
        simpa only [hempty, Finset.card_empty] using h.1
      exact (Nat.not_lt_zero _ himpossible).elim
  · intro hbad
    have hsupport :
        (badStrategy encoder agreementThreshold lanes strategy).support z =
          strategy.support z := by simp [badStrategy, hbad]
    constructor
    · rw [hsupport]
      exact hbad.1.1
    · intro x hx
      rw [hsupport] at hx
      exact hbad.1.2 x hx

/-- The cap counts valid unmatched responses of any challenge-dependent
strategy, even when jointly close components also exist for the lanes. -/
theorem degreeThree_bad_response_challenges_card_le
    (encoder : Message → Domain → K)
    (agreementThreshold challengeThreshold : Nat)
    (hcurve : DegreeThreeCurveDecodable
      encoder agreementThreshold challengeThreshold)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) :
    (goodChallenges encoder agreementThreshold lanes
      (badStrategy encoder agreementThreshold lanes strategy)).card ≤
        challengeThreshold := by
  classical
  by_contra hnot
  obtain ⟨components, selected, hselected, hlarge, honcurve⟩ :=
    hcurve lanes (badStrategy encoder agreementThreshold lanes strategy)
      (Nat.lt_of_not_ge hnot)
  obtain ⟨z, hzSelected, hzResolve⟩ :=
    exists_selected_not_resolving encoder lanes components selected hlarge
  have hgood := hselected hzSelected
  have hbad := (mem_badStrategy_good_iff encoder agreementThreshold lanes
    strategy z).mp hgood
  have hvalidMasked := (mem_goodChallenges_iff encoder agreementThreshold lanes
    (badStrategy encoder agreementThreshold lanes strategy) z).mp hgood
  have hsubsetMasked := support_subset_jointAgreement
    encoder agreementThreshold lanes
    (badStrategy encoder agreementThreshold lanes strategy)
    components z hvalidMasked (honcurve z hzSelected) hzResolve
  have hsupport : strategy.support z ⊆ jointAgreementSet encoder lanes components := by
    simpa [badStrategy, hbad] using hsubsetMasked
  have honcurveOriginal : CandidateOnCurve encoder strategy components z := by
    simpa [CandidateOnCurve, badStrategy] using honcurve z hzSelected
  exact hbad.2 ⟨components, hsupport, honcurveOriginal⟩

#print axioms mem_badStrategy_good_iff
#print axioms degreeThree_bad_response_challenges_card_le
end AspisWide.DegreeThreeMatched
