import TerminalV4PublicTerminalArithmeticSoundnessV6
import AspisR1.TerminalV4ActualBeginTerminalChallenges

/-! Specialize the successful terminal soundness result to the actual
successful begin record and the source's fieldwise `original_challenges`
copy.  Only copy-operand canonicality remains at this boundary. -/
set_option autoImplicit false
namespace AspisR1.TerminalV4PublicSoundnessWithBeginMuV2

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev Canonical := AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM
abbrev InputChallenges := AspisR1PublicPreparation.r1_wire.Challenges
abbrev TerminalChallenges := state_only_prefix.r0.Challenges
abbrev terminalChallenges :=
  AspisR1.TerminalV4ActualBeginTerminalChallenges.terminalChallenges

theorem terminal_success_arithmetic_of_actual_begin
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (before after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (challenges : InputChallenges)
    (hbegin : AspisR1PublicPreparation.r1_wire.begin D pre before =
      ok (.Ok challenges, after))
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (self : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array field.QM31 29#usize) 3#usize)
    (alpha : Array field.QM31 10#usize) (outerOut : field.QM31)
    (hsuccess : terminal_qm31_with_evaluators poseidonEval semanticEval self
      claims alpha (terminalChallenges challenges) =
        .ok (core.result.Result.Ok outerOut))
    (hpoint : ∀ i : Fin 10,
      AspisR1.TerminalV4EqualityValueResultRefinement.Canonical
        (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt)))
    (hoperands : ∀ sem selected composition c1 mask g h1Z copyActive,
      pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
        poseidonEval semanticEval sem selected alpha
        (terminalChallenges challenges).lambda
        (terminalChallenges challenges).chi
        (terminalChallenges challenges).theta =
          .ok (core.result.Result.Ok
            (composition, c1, mask, g, h1Z, copyActive)) →
      Canonical composition ∧ Canonical h1Z ∧ Canonical copyActive) :
    ∃ selected sem composition c1 mask g h1Z copyActive partOut,
      pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
        poseidonEval semanticEval sem selected alpha
        (terminalChallenges challenges).lambda
        (terminalChallenges challenges).chi
        (terminalChallenges challenges).theta =
          .ok (core.result.Result.Ok
            (composition, c1, mask, g, h1Z, copyActive)) ∧
      partOut = outerOut ∧ Canonical partOut ∧
      AspisR1.TerminalV4QM31Exact.decode partOut =
        (AspisR1.TerminalV4EqualityValueResultRefinement.expectedEquality
          (terminalChallenges challenges).zc alpha *
          AspisR1.TerminalV4QM31Exact.decode composition +
          AspisR1.TerminalV4QM31Exact.decode (terminalChallenges challenges).mu *
            AspisR1.TerminalV4QM31Exact.decode h1Z) +
        (AspisR1.TerminalV4QM31Exact.decode (terminalChallenges challenges).mu *
          AspisR1.TerminalV4QM31Exact.decode (terminalChallenges challenges).mu) *
        ((1 - AspisR1.TerminalV4QM31Exact.decode copyActive) *
          AspisR1.TerminalV4QM31Exact.decode h1Z) := by
  have hbeginCanonical := AspisR1PublicPreparation.ActualBeginSelectedCanonical.begin_challenges_selected_canonical
    D pre before after challenges hbegin
  have hzero : ∀ i : Fin 10,
      AspisR1.TerminalV4EqualityValueResultRefinement.Canonical
        ((terminalChallenges challenges).zc.val[i.val]'(by
          simpa [(terminalChallenges challenges).zc.property] using i.isLt)) := by
    intro i
    have hz := hbeginCanonical.2.2.2.2.2 i
    simpa only [terminalChallenges,
      AspisR1.TerminalV4ActualBeginTerminalChallenges.terminalChallenges,
      AspisR1.TerminalV4ActualBeginTerminalChallenges.selectedChallengeArray,
      AspisR1.TerminalV4EqualityValueResultRefinement.Canonical,
      AspisR1.TerminalV4EqualityValueLoop.Canonical,
      AspisR1.TerminalV4EqualityValueAdapter.Canonical,
      AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM,
      AspisR1.TerminalV4QM31Tower.CurrentCanonicalQM,
      AspisR1.TerminalV4TowerAdd.CanonicalQM,
      AspisR1.TerminalV4TowerAdd.P,
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM,
      AspisR1.ExtractedMaskTowerAdd.P,
      List.getElem_map] using hz
  have hmu : Canonical (terminalChallenges challenges).mu := by
    exact AspisR1.TerminalV4ActualBeginTerminalChallenges.begin_terminal_mu_canonical
      D pre before after challenges hbegin
  have hoperands' : ∀ sem selected composition c1 mask g h1Z copyActive,
      pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
        poseidonEval semanticEval sem selected alpha
        (terminalChallenges challenges).lambda
        (terminalChallenges challenges).chi
        (terminalChallenges challenges).theta =
          .ok (core.result.Result.Ok
            (composition, c1, mask, g, h1Z, copyActive)) →
      Canonical composition ∧ Canonical h1Z ∧ Canonical copyActive ∧
        Canonical (terminalChallenges challenges).mu := by
    intro sem selected composition c1 mask g h1Z copyActive hsuccessParts
    exact ⟨(hoperands sem selected composition c1 mask g h1Z copyActive
      hsuccessParts).1,
      (hoperands sem selected composition c1 mask g h1Z copyActive
        hsuccessParts).2.1,
      (hoperands sem selected composition c1 mask g h1Z copyActive
        hsuccessParts).2.2, hmu⟩
  exact AspisR1.TerminalV4PublicTerminalArithmeticSoundness.terminal_success_has_canonical_arithmetic_parts
      poseidonEval semanticEval self claims alpha (terminalChallenges challenges)
      outerOut hsuccess hzero hpoint hoperands'

#print axioms terminal_success_arithmetic_of_actual_begin
end AspisR1.TerminalV4PublicSoundnessWithBeginMuV2
