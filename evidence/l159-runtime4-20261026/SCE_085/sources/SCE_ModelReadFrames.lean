import SCE_SingleRuntime
import F3T_CanonicalChecks
import OraclePortReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_ModelReadFrames
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment

/-- Model accepted original executions contain all three commitment frames.
The constructor validity is derived from canonical accepted schedule. -/
theorem frames (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (accepted : (eval H (original D (F3T_Canon.canon P))).2.2 = true) :
    let v := view (eval H (original D (F3T_Canon.canon P)))
    Read v.1 (RawCommitmentFrameReplay.frameFromView v 0) ∧
    Read v.1 (RawCommitmentFrameReplay.frameFromView v 2) ∧
    Read v.1 (RawCommitmentFrameReplay.frameFromView v 30) := by
  let CP := F3T_Canon.canon P
  let v := view (eval H (original D CP))
  have valid : RawCutWordsFromRunExecutableBin.ValidPrefix v := by
    intro row small
    simpa only [v,CP,view,original_eval] using
      F3T_CanonicalChecks.canonical_valid D P H accepted row (by omega)
  have equal := RawCommitmentFrameReplayCorrect.frameFromView_commitments_eq D v valid
  dsimp only
  rw [equal.1,equal.2.1,equal.2.2]
  have read (row : Nat) (small : row < 33) :
      Read v.1 (RawCutWordsFromView.frameFromView D v row) := by
    dsimp only [v]
    rw [F3T_Projection.original_view]
    rw [OraclePortReplay.frameFromView_eq D _ _ H row (by omega)]
    exact OraclePortReplay.frame_read D _ _ H row small
  exact ⟨read 0 (by decide),read 2 (by decide),read 30 (by decide)⟩

#print axioms frames
end AspisR1.SCE_ModelReadFrames
end
