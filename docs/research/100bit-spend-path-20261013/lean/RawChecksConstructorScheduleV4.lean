import R1LiteralAcceptanceTerminal
import R1LiteralOpeningPrefixFacts
import R1LiteralSemanticIndex
import R1LiteralSemanticNoHit
import R1LiteralMatchingFacts
import R1LiteralStageFacts
import R1LiteralReadAtFacts

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawChecksConstructorSchedule

open AspisR1.LiteralTranscript
open AspisR1.LiteralAcceptanceTerminal
open AspisR1.LiteralOpeningPrefixFacts
open AspisR1.LiteralSemanticIndex
open AspisR1.LiteralSemanticNoHit
open AspisR1.LiteralMatchingFacts
open AspisR1.LiteralStageFacts
open AspisR1.LiteralReadAtFacts
open AspisR1.LiteralOpeningStages
open AspisR1.LiteralOpeningView
open AspisR1.LiteralMatchingData
open AspisR1.LiteralSemanticPrefix
open AspisR1.LiteralReadAtFacts
open AspisR1.LiteralTranscript

private theorem rowEntry_of_valid_getElem
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) (hi : i < rs.length)
    (hv : LiteralTranscript.valid i (rs[i]'hi).1) :
    ∃ m c, rs[i]? = some (m, c) ∧ LiteralTranscript.valid i m := by
  exact ⟨(rs[i]'hi).1, (rs[i]'hi).2, List.getElem?_eq_getElem hi, hv⟩

private theorem valid_of_readAt
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) (hi : i < rs.length) {A : Type}
    (decode : AspisV8R19.DuplexFrames.Bytes → Option A) (value : A)
    (h : LiteralOpeningStages.readAt rs i decode = some value) :
    LiteralTranscript.valid i (rs[i]'hi).1 := by
  exact LiteralIndexedPrefix.readAt_success_index_valid rs i hi decode value h

/-- Successful opening and matching readers force the literal constructor
schedule on rows 0 through 30. This extracts only syntax validity; it makes
no no-hit, acceptance, or semantic soundness claim. -/
theorem checks_force_constructor_schedule
    (pub : LiteralTranscript.Public)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (checks : LiteralAcceptanceTerminal.Checks pub rs)
    (hlen : 32 ≤ rs.length) :
    ∀ i, i ≤ 30 → ∃ m c, rs[i]? = some (m, c) ∧ LiteralTranscript.valid i m := by
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hcommon, hstaged, hrow31, hword, hgamma, hkappa, halpha0, halpha1, _⟩ :=
      LiteralMatchingFacts.read_success_components rs checks.data checks.matchingRead
  obtain ⟨hprefixLen, _hc1, _hc2, hsemantic, _hword⟩ :=
    LiteralOpeningPrefixFacts.read_prefix_components rs common hcommon
  have hsemanticLength := LiteralSemanticPrefix.read_length
    LiteralOpeningView.eK 0 (rs.take 25) common.semantic hsemantic
  have hsplit : rs.take 25 ++ rs.drop 25 = rs := List.take_append_drop 25 rs
  have hgammaRows := LiteralReadAtFacts.readGamma_current rs staged.toFirst.toKappa.toGamma
    (LiteralStageFacts.readSecond_gamma rs staged hstaged)
  have hkappaRow := LiteralReadAtFacts.readKappa_current rs staged.toFirst.toKappa
    (LiteralStageFacts.readSecond_kappa rs staged hstaged)
  have hfirstRow := LiteralReadAtFacts.readFirst_current rs staged.toFirst
    (LiteralStageFacts.readSecond_first rs staged hstaged)
  have hsecondRow := LiteralReadAtFacts.readSecond_current rs staged hstaged
  intro i hi
  by_cases hsmall : i < 25
  · have hsmallIndex : i < (rs.take 25).length := by
      rw [hprefixLen]
      exact hsmall
    obtain ⟨hrow, parsed, challenge, hparse, _hchallenge, _houtput⟩ :=
      LiteralSemanticIndex.read_index LiteralOpeningView.eK 0 (rs.take 25)
        common.semantic hsemantic i hsmallIndex
    have hparse' := by simpa only [Nat.zero_add] using hparse
    have hv := LiteralSemanticNoHit.parseMessage_valid LiteralOpeningView.eK
      ⟨i, by omega⟩ ((rs.take 25)[i]'hsmallIndex).1 parsed hparse'
    have htakeGet : (rs.take 25)[i]? = some ((rs.take 25)[i]'hsmallIndex) :=
      List.getElem?_eq_getElem hsmallIndex
    have htakeToFull : (rs.take 25)[i]? = rs[i]? := by
      have happ := List.getElem?_append_left (l₂ := rs.drop 25) hsmallIndex
      rw [hsplit] at happ
      exact happ.symm
    obtain ⟨m, c, hget, hv'⟩ :=
      rowEntry_of_valid_getElem (rs.take 25) i hsmallIndex hv
    have hfullGet : rs[i]? = some (m, c) := htakeToFull.symm.trans hget
    exact ⟨m, c, hfullGet, hv'⟩
  · have hi : i < rs.length := by omega
    have he := rowEntry_of_valid_getElem rs i hi
    have h25 := valid_of_readAt rs 25 (by omega)
      (AspisR1.CircleRecordCodec.decode 0) staged.toFirst.toKappa.toGamma.row25
      hgammaRows.1
    have h26 := valid_of_readAt rs 26 (by omega)
      (AspisR1.CircleRecordCodec.decode 1) staged.toFirst.toKappa.toGamma.row26
      hgammaRows.2.1
    have h27 := valid_of_readAt rs 27 (by omega)
      (AspisR1.OpeningRecordCodec.decode .gamma) staged.toFirst.toKappa.toGamma.row27
      hgammaRows.2.2
    have h28 := valid_of_readAt rs 28 (by omega)
      (AspisR1.OpeningRecordCodec.decode .kappa) staged.toFirst.toKappa.row28 hkappaRow
    have h29 := valid_of_readAt rs 29 (by omega)
      (AspisR1.OpeningRecordCodec.decode .first) staged.toFirst.row29 hfirstRow
    have h30 := valid_of_readAt rs 30 (by omega)
      (AspisR1.OpeningRecordCodec.decode .second) staged.row30 hsecondRow
    have hrows : i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 := by omega
    rcases hrows with hi25 | hi26 | hi27 | hi28 | hi29 | hi30
    · subst i; exact he h25
    · subst i; exact he h26
    · subst i; exact he h27
    · subst i; exact he h28
    · subst i; exact he h29
    · subst i; exact he h30

#print axioms checks_force_constructor_schedule
end AspisR1.RawChecksConstructorSchedule
end
