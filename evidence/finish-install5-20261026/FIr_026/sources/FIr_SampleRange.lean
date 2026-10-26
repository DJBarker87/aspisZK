import F3M_OpeningChallenges
import F3J_SamplerStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_SampleRange
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open TranscriptView

def ordinary (c : LiteralTranscript.Challenge) : LiteralTranscript.E :=
  match c.1 with | .ordinary x => x | .queries _ => 0

def InBase (x : LiteralTranscript.E) : Prop :=
  LiteralOpeningView.eK (SelectedChallengeMap.rhoOf x)=x

theorem zero : InBase 0 := by exact map_zero _

theorem sigma (row : Nat) (below : row<25) (state : State) :
    InBase (SelectedTranscriptParams.params.σ row state) := by
  change InBase (SelectedChallengeMap.sigma row state)
  rw [SelectedChallengeMap.semantic_row row below]
  rfl

/-- Even invalid messages yield zero in the ordinary-value projection.
Every ordinary challenge in the first 25 sampler rows lies in the base. -/
theorem sampled (H : Bytes → State) (row : Nat) (below : row<25)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    InBase (ordinary (eval H (LiteralByteSampler.samp row P m).toProgram).2) := by
  rw [LiteralByteSampler.eval_eq]
  change InBase (ordinary (eval (fun a => H a.toBytes)
    (UnifiedSampler.samp SelectedTranscriptParams.params _ row
      (LiteralTranscript.erasePrefix P) (LiteralTranscript.erase m)).toProgram).2)
  cases row with
  | zero =>
    cases erased : LiteralTranscript.erase m with
    | initial root =>
      rw [UnifiedSampler.row_zero,DuplexSamplers.initial_eval]
      exact sigma 0 (by decide) _
    | payload b =>
      simp only [UnifiedSampler.samp,UnifiedSampler.invalid,Sampler.toProgram,eval,ordinary]
      exact zero
  | succ row =>
    cases erased : LiteralTranscript.erase m with
    | initial root =>
      simp only [UnifiedSampler.samp,UnifiedSampler.invalid,Sampler.toProgram,eval,ordinary]
      exact zero
    | payload b =>
      rw [UnifiedSampler.row_ordinary _ _ (row+1) (by omega) (by omega) (by omega),DuplexSamplers.plain_eval]
      exact sigma _ below _

#print axioms zero
#print axioms sigma
#print axioms sampled
end AspisR1.FIr_SampleRange
end
