import AspisPairResidualDensity
import R1LiteralQueryRhoSupport

/-! The Aspis analogue of R1's `LiteralQueryRhoSupport.large_support`: no hit
of R1's row-31 query event, no hit of the row-32 PAIR event, and the two
batched equalities (in place of R1's 22 per-query first-fold equalities and
its residual batch) force large matching support for the same literal data.

Kind of result: DETERMINISTIC MODEL THEOREM in R1's literal-transcript model,
for the data and queries read from the prefix. It is the terminal step the
Aspis classifier's rows 31 and 32 feed. Accepted-execution coverage (that an
accepted Aspis run yields these hypotheses for the compiled rows) and
probability are separate obligations, open for Aspis. -/

set_option autoImplicit false
noncomputable section
namespace AspisPairResidual.Support

open scoped BigOperators
open AspisR1 AspisR1.LiteralTranscript
open AspisV8R19.SourceDuplexStep
abbrev E := LiteralTranscript.E
attribute [local irreducible] MatchingSupport.matchingSet QueryResidualBridge.rhoBad
  QueryResidualBridge.residuals MatchingSupport.match0
  LiteralClassifier.bad LiteralQueryDensity.bad LiteralRhoDensity.bad
  AspisPairResidual.pairBad AspisPairResidual.firstResiduals

theorem large_support (P : Prefix) (m31 : Message)
    (xs : List Nat) (s31 : State) (v : E)
    (d : MatchingSupport.Data E) (q : Fin 22 → Fin 262144)
    (hround : P.round = 31)
    (hv31 : LiteralTranscript.valid 31 m31)
    (hdata : LiteralMatchingData.atQuery P m31 = some d)
    (hdecode : LiteralQueryRead.decode xs = some q)
    (hno31 : ¬ LiteralClassifier.bad P m31
      (TranscriptView.Value.queries (.ok xs), s31))
    (hno32 : ¬ AspisPairResidual.Row32.bad
      (P.ext m31 (TranscriptView.Value.queries (.ok xs), s31)) v)
    (h0 : ∑ j : Fin 22,
      (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf v)) ^ j.val *
        AspisPairResidual.firstResiduals d q j = 0)
    (hbatch : ∑ j : Fin 22,
      (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf v)) ^ j.val *
        QueryResidualBridge.residuals d q j = 0) :
    9558 ≤ (MatchingSupport.matchingSet d).card := by
  let P32 := P.ext m31 (TranscriptView.Value.queries (.ok xs), s31)
  have hd32 : LiteralMatchingData.beforeRho P32 = some d := by
    rw [LiteralQueryContext.beforeRho_ext_eq_atQuery P m31 _ hround]
    exact hdata
  have hq32 : LiteralQueryRead.queriesAt P32.rounds 31 = some q :=
    LiteralQueryCurrentRead.queriesAt_current P m31 xs s31 q hround hdecode
  have hread : LiteralRhoDensity.read P32 = some (d, q) := by
    simp [LiteralRhoDensity.read, hd32, hq32]
  have hrho : SelectedChallengeMap.rhoOf v ∉
      AspisPairResidual.pairBad LiteralOpeningView.eK d q := by
    intro hbad
    apply hno32
    show AspisPairResidual.Row32.bad P32 v
    simp only [AspisPairResidual.Row32.bad, hread]
    exact hbad
  have hmatches := AspisPairResidual.pair_queries_match LiteralOpeningView.eK d q
    (SelectedChallengeMap.rhoOf v) hrho h0 hbatch
  by_contra hsmall
  have hcard : (MatchingSupport.matchingSet d).card ≤ 9557 := by omega
  have hquery := (LiteralQueryBinding.query_event_iff P m31 xs q d s31
    hround hv31 hdata hdecode).mpr ⟨hcard, hmatches⟩
  apply hno31
  simpa only [LiteralClassifier.bad, hround, Nat.reduceLT, if_false] using hquery

#print axioms large_support

end AspisPairResidual.Support
end
