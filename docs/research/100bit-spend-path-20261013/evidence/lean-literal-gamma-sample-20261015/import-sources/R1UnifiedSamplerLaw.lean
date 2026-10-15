import R1UnifiedSampler
import R1QueryNextLaw

/-! Independent-answer law for each valid non-query unified sampler row. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSampler

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

theorem unified_law (p : Params M Cv L) (hD : 5 ≤ p.D) (i : Nat)
    (P : Prefix M Cv L) (m : Message M)
    (obs : TranscriptView.Challenge Cv → ℚ)
    (hi31 : i ≠ 31) (hm : messageValid i m) :
    independentMean (samp p hD i P m).toProgram (fun w => obs w.2) =
      mean (fun b => mean (fun x =>
        obs (TranscriptView.liftChallenge (p.σ i b, x)))) := by
  cases i with
  | zero =>
      cases m with
      | initial c1 =>
          rw [row_zero]
          exact DuplexSamplers.initial_law p
            (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1)
            (PublicInitFrame.row0 p hD) 0 TranscriptView.liftChallenge obs
      | payload msg => simp [messageValid] at hm
  | succ j =>
      cases m with
      | initial c1 => simp [messageValid] at hm
      | payload msg =>
          by_cases h26 : j + 1 = 26
          · have hj : j = 25 := by omega
            subst j
            rw [row_reseed]
            exact DuplexSamplers.reseeded_law p (absorb p 26 P msg)
              (OpeningReseedFrame.addr P.statement.tag
                (by have := P.statement.initFits; omega))
              26 TranscriptView.liftChallenge obs
          · by_cases h31 : j + 1 = 31
            · exact False.elim (hi31 (by omega))
            · rw [row_ordinary p hD (j + 1) (by omega) (by omega)
                (by omega) P msg]
              exact DuplexSamplers.plain_law p (absorb p (j + 1) P msg)
                (j + 1) TranscriptView.liftChallenge obs

#print axioms unified_law

end AspisR1.UnifiedSampler
end
