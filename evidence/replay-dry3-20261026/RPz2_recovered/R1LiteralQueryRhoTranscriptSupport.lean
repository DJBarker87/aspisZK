import R1LiteralQueryRhoSupport
import R1LiteralReadStability
import R1GenericNoHitIndex

/-! List plumbing for specializing the query/rho support implication to a
full literal transcript. This remains a deterministic model statement. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralQueryRhoTranscriptSupport

open AspisR1.LiteralTranscript
open AspisR1.TranscriptView
open AspisV8R19.SourceDuplexStep

attribute [local irreducible] LiteralClassifier.bad MatchingSupport.matchingSet
  MatchingSupport.match0 QueryResidualBridge.residuals

theorem atQuery_current_eq_read
    (pub : LiteralTranscript.Public)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (hlen : 32 ≤ rs.length) :
    LiteralMatchingData.atQuery ⟨pub, rs.take 31⟩ (rs[31]'(by omega)).1 =
      LiteralMatchingData.read rs := by
  have h31 : (rs.take 31).length = 31 := by simp; omega
  have h32 : (rs.take 32).length = 32 := by simp; omega
  have hstable := LiteralReadStability.matchingData_append_stable
    (rs.take 32) (rs.drop 32) (by omega)
  have hdecomp : rs.take 32 ++ rs.drop 32 = rs := List.take_append_drop 32 rs
  rw [hdecomp] at hstable
  have htake : rs.take 32 = rs.take 31 ++ [rs[31]'(by omega)] := by
    rw [List.take_succ_eq_append_getElem (by omega)]
  rw [LiteralMatchingData.atQuery, LiteralOpeningEvents.withMessage]
  rw [hstable, htake]
  have hc := LiteralQueryContext.matchingData_challenge_independent
    (rs.take 31) (rs[31]'(by omega)).1 (rs[31]'(by omega)).2
    (Value.ordinary 0, 0) h31
  simpa only using hc.symm

theorem large_support_of_read_noHit
    (pub : LiteralTranscript.Public)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (hlen : 33 ≤ rs.length)
    (d : MatchingSupport.Data AspisWideTower.WideExact)
    (hread : LiteralMatchingData.read rs = some d)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub [] rs)
    (m31 : LiteralTranscript.Message) (xs : List Nat)
    (s31 : State) (m32 : LiteralTranscript.Message)
    (rho : AspisWideTower.WideExact) (s32 : State)
    (h31 : rs[31]? = some (m31, (Value.queries (.ok xs), s31)))
    (h32 : rs[32]? = some (m32, (Value.ordinary rho, s32)))
    (hvalid31 : LiteralTranscript.valid 31 m31)
    (hvalid32 : LiteralTranscript.valid 32 m32)
    (q : Fin 22 → Fin 262144)
    (hdecode : LiteralQueryRead.decode xs = some q)
    (hfirst : ∀ j, MatchingSupport.match0 d (q j))
    (hbatch : ∑ j : Fin 22,
      (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf rho)) ^ j.val *
        QueryResidualBridge.residuals d q j = 0) :
    9558 ≤ (MatchingSupport.matchingSet d).card := by
  let P : LiteralTranscript.Prefix := ⟨pub, rs.take 31⟩
  have hround : P.round = 31 := by simp [P, FS.Prefix.round]; omega
  have hi31 : 31 < rs.length := by omega
  have hi32 : 32 < rs.length := by omega
  have hentry31 : rs[31]'hi31 = (m31, (Value.queries (.ok xs), s31)) := by
    exact Option.some.inj ((List.getElem?_eq_getElem hi31).symm.trans h31)
  have hentry32 : rs[32]'hi32 = (m32, (Value.ordinary rho, s32)) := by
    exact Option.some.inj ((List.getElem?_eq_getElem hi32).symm.trans h32)
  have hdata : LiteralMatchingData.atQuery P m31 = some d := by
    have hd := atQuery_current_eq_read pub rs (by omega)
    rw [hentry31] at hd
    exact hd.trans hread
  have hno31 : ¬ LiteralClassifier.bad P m31
      (Value.queries (.ok xs), s31) := by
    have h := GenericNoHitIndex.not_bad_at_index LiteralClassifier.bad pub rs 31 hi31 hno
    simpa only [P, hentry31] using h
  let P32 := P.ext m31 (Value.queries (.ok xs), s31)
  have hno32 : ¬ LiteralClassifier.bad P32 m32
      (Value.ordinary rho, s32) := by
    have h := GenericNoHitIndex.not_bad_at_index LiteralClassifier.bad pub rs 32 hi32 hno
    have htake32 : rs.take 32 = P32.rounds := by
      rw [List.take_succ_eq_append_getElem (by omega)]
      simp only [P32, P, FS.Prefix.ext, hentry31]
    rw [htake32, hentry32] at h
    exact h
  exact LiteralQueryRhoSupport.large_support P m31 m32 xs s31 s32 rho d q
    hround hvalid31 hvalid32 hdata hdecode hno31 hno32 hfirst hbatch

#print axioms atQuery_current_eq_read
#print axioms large_support_of_read_noHit

end AspisR1.LiteralQueryRhoTranscriptSupport
end
