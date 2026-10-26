import R1LiteralQueryBinding
import R1LiteralRhoBinding
import R1LiteralQueryCurrentRead
import R1LiteralQueryContext

/-! The two final no-hit conditions and the actual residual checks force
large matching support for the same literal data. This is a deterministic
conditional implication; accepted-execution coverage and probability are
separate obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralQueryRhoSupport

open scoped BigOperators
open LiteralTranscript
open AspisV8R19.SourceDuplexStep
abbrev E := LiteralTranscript.E
-- This proof transports predicates, without evaluating the underlying words.
attribute [local irreducible] MatchingSupport.matchingSet QueryResidualBridge.rhoBad
  QueryResidualBridge.residuals MatchingSupport.match0
  LiteralClassifier.bad LiteralQueryDensity.bad LiteralRhoDensity.bad

theorem large_support (P : Prefix) (m31 m32 : Message)
    (xs : List Nat) (s31 s32 : State) (v : E)
    (d : MatchingSupport.Data E) (q : Fin 22 → Fin 262144)
    (hround : P.round = 31)
    (hv31 : LiteralTranscript.valid 31 m31)
    (hv32 : LiteralTranscript.valid 32 m32)
    (hdata : LiteralMatchingData.atQuery P m31 = some d)
    (hdecode : LiteralQueryRead.decode xs = some q)
    (hno31 : ¬ LiteralClassifier.bad P m31
      (TranscriptView.Value.queries (.ok xs), s31))
    (hno32 : ¬ LiteralClassifier.bad
      (P.ext m31 (TranscriptView.Value.queries (.ok xs), s31)) m32
      (TranscriptView.Value.ordinary v, s32))
    (hfirst : ∀ j, MatchingSupport.match0 d (q j))
    (hbatch : ∑ j : Fin 22,
      (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf v)) ^ j.val *
        QueryResidualBridge.residuals d q j = 0) :
    9558 ≤ (MatchingSupport.matchingSet d).card := by
  let P32 := P.ext m31 (TranscriptView.Value.queries (.ok xs), s31)
  have hlen : P.rounds.length = 31 := hround
  have hr32 : P32.round = 32 := by
    simp only [P32, FS.Prefix.round, FS.Prefix.ext, List.length_append,
      List.length_singleton, hlen]
  have hd32 : LiteralMatchingData.beforeRho P32 = some d := by
    rw [LiteralQueryContext.beforeRho_ext_eq_atQuery P m31 _ hround]
    exact hdata
  have hq32 : LiteralQueryRead.queriesAt P32.rounds 31 = some q :=
    LiteralQueryCurrentRead.queriesAt_current P m31 xs s31 q hround hdecode
  have hrho : SelectedChallengeMap.rhoOf v ∉
      QueryResidualBridge.rhoBad LiteralOpeningView.eK d q := by
    intro hbad
    apply hno32
    exact (LiteralRhoBinding.rho_event_iff P32 m32 v s32 d q hr32 hv32 hd32 hq32).mpr hbad
  have hmatches := QueryResidualBridge.queries_match LiteralOpeningView.eK d q
    (SelectedChallengeMap.rhoOf v) hrho hfirst hbatch
  by_contra hsmall
  have hcard : (MatchingSupport.matchingSet d).card ≤ 9557 := by omega
  have hquery := (LiteralQueryBinding.query_event_iff P m31 xs q d s31
    hround hv31 hdata hdecode).mpr ⟨hcard, hmatches⟩
  apply hno31
  simpa only [LiteralClassifier.bad, hround, Nat.reduceLT, if_false] using hquery

#print axioms large_support

end AspisR1.LiteralQueryRhoSupport
end
