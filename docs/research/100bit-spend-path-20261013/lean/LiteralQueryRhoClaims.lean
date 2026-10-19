import R1LiteralQueryRhoSupport

/-! Conditional deterministic composition from the query/rho support bound to
matching claims. This adds only the existing `Good` and `AcceptedPairing`
conditions; it is not a source, acceptance, or probability theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralQueryRhoClaims

open LiteralTranscript
open AspisV8R19.SourceDuplexStep

abbrev E := LiteralTranscript.E

-- Compose named predicates without expanding the concrete field/word model.
attribute [local irreducible] MatchingSupport.matchingSet MatchingSupport.Good
  MatchingSupport.Claims MatchingSupport.AcceptedPairing MatchingSupport.match0
  QueryResidualBridge.residuals LiteralClassifier.bad

theorem claims_of_good (P : Prefix) (m31 m32 : Message)
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
        QueryResidualBridge.residuals d q j = 0)
    (hgood : MatchingSupport.Good d)
    (haccepted : MatchingSupport.AcceptedPairing d) :
    MatchingSupport.Claims d :=
  MatchingSupport.large_matching_implies_claims d hgood haccepted
    (LiteralQueryRhoSupport.large_support P m31 m32 xs s31 s32 v d q
      hround hv31 hv32 hdata hdecode hno31 hno32 hfirst hbatch)

#print axioms claims_of_good

end AspisR1.LiteralQueryRhoClaims
end
