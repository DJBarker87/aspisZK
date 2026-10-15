import R1LiteralMatchingFacts
import R1SelectedOpeningPairing

/-! A successful literal matching-data read is paired exactly when its
assembled coefficient checks hold. This is a model identity only; it does not
identify the reader with a Rust acceptance path. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralPairingChecks

open AspisR1.LiteralTranscript
open AspisR1.LiteralOpeningView
open AspisR1.LiteralOpeningStages
open AspisR1.LiteralChallengeRead
open AspisR1.OpeningRecordCodec
open AspisR1.SelectedOpeningData
open AspisR1.MatchingSupport

abbrev E := AspisR1.LiteralMatchingData.E

def checks
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) : Prop :=
  ∃ (common : LiteralOpeningView.View)
    (staged : LiteralOpeningStages.Second)
    (row31 : OpeningRecordCodec.Payload .final)
    (word : LiteralTranscript.VWord)
    (gamma kappa alpha0 alpha1 : E),
    LiteralOpeningView.read rs = some common ∧
    LiteralOpeningStages.readSecond rs = some staged ∧
    LiteralOpeningStages.readAt rs 31 (OpeningRecordCodec.decode .final) = some row31 ∧
    LiteralTranscript.vAt rs = some word ∧
    LiteralChallengeRead.ordinaryAt rs 27 = some gamma ∧
    LiteralChallengeRead.ordinaryAt rs 28 = some kappa ∧
    LiteralChallengeRead.ordinaryAt rs 29 = some alpha0 ∧
    LiteralChallengeRead.ordinaryAt rs 30 = some alpha1 ∧
    SelectedOpeningPairing.coefficientChecks
      (LiteralMatchingFacts.payloads staged row31)
      common.functionals common.baseFunctional gamma kappa alpha0 alpha1

theorem acceptedPairing_iff_checks
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (d : MatchingSupport.Data E)
    (hread : LiteralMatchingData.read rs = some d) :
    MatchingSupport.AcceptedPairing d ↔ checks rs := by
  constructor
  · intro haccepted
    obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
      hcommon, hstaged, hrow31, hword, hgamma, hkappa, halpha0, halpha1, hdata⟩ :=
      LiteralMatchingFacts.read_success_components rs d hread
    rw [hdata] at haccepted
    refine ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
      hcommon, hstaged, hrow31, hword, hgamma, hkappa, halpha0, halpha1, ?_⟩
    exact (SelectedOpeningPairing.acceptedPairing_iff_coefficientChecks
      (LiteralMatchingFacts.payloads staged row31) common.word word
      common.functionals common.baseFunctional gamma kappa alpha0 alpha1).mp haccepted
  · rintro ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
      hcommon, hstaged, hrow31, hword, hgamma, hkappa, halpha0, halpha1,
      hchecks⟩
    have hread' := hread
    simp only [LiteralMatchingData.read, hcommon, hstaged, hrow31, hword,
      hgamma, hkappa, halpha0, halpha1, Option.bind_eq_bind,
      Option.bind_some, pure, Pure.pure] at hread'
    have hdata : d = SelectedOpeningData.data
        (LiteralMatchingFacts.payloads staged row31) common.word word
        common.functionals common.baseFunctional gamma kappa alpha0 alpha1 :=
      (Option.some.inj hread').symm
    rw [hdata]
    exact (SelectedOpeningPairing.acceptedPairing_iff_coefficientChecks
      (LiteralMatchingFacts.payloads staged row31) common.word word
      common.functionals common.baseFunctional gamma kappa alpha0 alpha1).mpr hchecks

#print axioms acceptedPairing_iff_checks

end AspisR1.LiteralPairingChecks
end
