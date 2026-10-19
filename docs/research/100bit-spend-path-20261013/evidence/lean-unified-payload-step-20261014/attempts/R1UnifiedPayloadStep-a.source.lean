import R1UnifiedSampler
import R1DuplexSamplers
import R1OpeningReseedFrame

/-! State-step and read-set facts for symbolic ordinary and reseeded R1
payload rows. The prefix remains arbitrary. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedPayloadStep

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

theorem payload_step (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (i : Nat) (hi0 : i ≠ 0) (hi26 : i ≠ 26)
    (hi31 : i ≠ 31) (P : UnifiedSampler.Prefix M Cv L) (m : M) :
    (eval H (UnifiedSampler.samp p hD i P (.payload m)).toProgram).2.2 =
      H (advanceA p (H (UnifiedSampler.absorb p i P m))) := by
  rw [UnifiedSampler.row_ordinary p hD i hi0 hi26 hi31 P m]
  rw [DuplexSamplers.plain_eval]
  rfl

theorem payload_reads (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (i : Nat) (hi0 : i ≠ 0) (hi31 : i ≠ 31)
    (P : UnifiedSampler.Prefix M Cv L) (m : M) :
    let a := UnifiedSampler.absorb p i P m
    a ∈ (eval H (UnifiedSampler.samp p hD i P (.payload m)).toProgram).1.map Prod.fst ∧
    squeezeA p (H a) ∈
      (eval H (UnifiedSampler.samp p hD i P (.payload m)).toProgram).1.map Prod.fst ∧
    advanceA p (H a) ∈
      (eval H (UnifiedSampler.samp p hD i P (.payload m)).toProgram).1.map Prod.fst := by
  dsimp
  let a := UnifiedSampler.absorb p i P m
  by_cases h26 : i = 26
  · subst i
    rw [UnifiedSampler.row_reseed p hD P m]
    simp [DuplexSamplers.reseeded, Sampler.toProgram, eval, a]
  · rw [UnifiedSampler.row_ordinary p hD i hi0 h26 hi31 P m]
    simp [DuplexSamplers.plain, Sampler.toProgram, eval, a]

theorem reseed_step (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (P : UnifiedSampler.Prefix M Cv L) (m : M) :
    (eval H (UnifiedSampler.samp p hD 26 P (.payload m)).toProgram).2.2 =
      H (OpeningReseedFrame.addr P.statement.tag
        (by have := P.statement.initFits; omega)
        (H (advanceA p (H (UnifiedSampler.absorb p 26 P m))))) := by
  rw [UnifiedSampler.row_reseed p hD P m]
  rw [DuplexSamplers.reseeded_eval]
  rfl

theorem reseed_read (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (P : UnifiedSampler.Prefix M Cv L) (m : M) :
    OpeningReseedFrame.addr P.statement.tag
      (by have := P.statement.initFits; omega)
      (H (advanceA p (H (UnifiedSampler.absorb p 26 P m)))) ∈
        (eval H (UnifiedSampler.samp p hD 26 P (.payload m)).toProgram).1.map Prod.fst := by
  rw [UnifiedSampler.row_reseed p hD P m]
  simp [DuplexSamplers.reseeded, Sampler.toProgram, eval]

#print axioms payload_step
#print axioms payload_reads
#print axioms reseed_step
#print axioms reseed_read

end AspisR1.UnifiedPayloadStep
end
