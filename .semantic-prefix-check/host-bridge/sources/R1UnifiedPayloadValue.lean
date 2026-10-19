import R1UnifiedSampler

/-! The ordinary challenge value emitted by every valid nonzero,
non-query payload row, with the prefix left symbolic. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedPayloadValue

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep TranscriptView

variable {M Cv : Type} {L : Nat}

theorem sampler_payload_value (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (i : Nat) (hi0 : i ≠ 0) (hi31 : i ≠ 31)
    (P : UnifiedSampler.Prefix M Cv L) (m : M) :
    (eval H (UnifiedSampler.samp p hD i P (.payload m)).toProgram).2.1 =
      Value.ordinary (p.σ i (H (squeezeA p (H (UnifiedSampler.absorb p i P m))))) := by
  cases i with
  | zero => exact False.elim (hi0 rfl)
  | succ j =>
      by_cases h26 : j + 1 = 26
      · have hj : j = 25 := by omega
        subst j
        rw [UnifiedSampler.row_reseed]
        rw [DuplexSamplers.reseeded_eval]
        rfl
      · rw [UnifiedSampler.row_ordinary p hD (j + 1) (by omega)
          (by omega) (by omega) P m]
        rw [DuplexSamplers.plain_eval]
        rfl

#print axioms sampler_payload_value

end AspisR1.UnifiedPayloadValue
end
