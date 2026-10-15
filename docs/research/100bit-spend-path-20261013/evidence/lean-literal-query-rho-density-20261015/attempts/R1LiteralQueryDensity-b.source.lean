import R1LiteralMatchingData
import R1UnifiedQueryDensity
import AspisV8R19.R572SequentialWordMass

/-! A row-31 density adapter using the selected set read from literal entries.
The callback is fixed by the supplied prefix/message. This is an independent
row bound only; it does not establish the selected set's support premises or
terminal acceptance. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralQueryDensity

open FS FS2
open AspisV8R19.R572SequentialWordMass
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw
attribute [local instance] Classical.propDecidable

open AspisR1.LiteralTranscript
open AspisV8R19.SourceDuplexStep

def selectedSet (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    Option (Finset (Fin 262144)) :=
  (LiteralMatchingData.atQuery P m).map MatchingSupport.matchingSet

def bad (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (ch : LiteralTranscript.Challenge) : Prop :=
  LiteralTranscript.valid P.round m ∧
    UnifiedQueryDensity.queryBad (fun _ _ _ => selectedSet P m)
      (LiteralTranscript.erasePrefix P) (LiteralTranscript.erase m) (fun _ => none) ch

theorem row31_density (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hround : P.round = 31) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (bad P m v.2)) ≤ UnifiedQueryDensity.queryCap := by
  have hcap : 0 ≤ UnifiedQueryDensity.queryCap := by
    unfold UnifiedQueryDensity.queryCap
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  by_cases hv : LiteralTranscript.valid P.round m
  · have hprefix : (LiteralTranscript.erasePrefix P).rounds.length = 31 := by
      change (LiteralTranscript.erasePrefix P).round = 31
      rw [LiteralTranscript.erasePrefix_round, hround]
    have hdensity := UnifiedQueryDensity.query_density_bound
      SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
      (fun _ _ _ => selectedSet P m) (fun _ => none) 31 (LiteralTranscript.erasePrefix P)
      (LiteralTranscript.erase m) (by omega) hprefix
    rw [hround]
    unfold LiteralTranscript.samp
    simpa [bad, hv, hprefix] using hdensity
  · simp only [bad, hv, false_and, indicator_false, independentMean_const]
    exact hcap

#print axioms row31_density

end AspisR1.LiteralQueryDensity
end
