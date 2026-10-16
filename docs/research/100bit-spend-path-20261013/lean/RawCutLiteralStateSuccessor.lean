import R1LiteralByteSampler
import R1QuerySamplerBridge
import R1SelectedTranscriptParams

/-! Exact state component returned by each literal sampler row.  These are
sampler semantics only; no frame-order or source-refinement claim is made. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutLiteralStateSuccessor

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.LiteralTranscript
open AspisR1.UnifiedSampler
open AspisR1.DuplexSamplers
open AspisR1.QuerySamplerBridge

private def params := SelectedTranscriptParams.params
private theorem params_D : 5 ≤ params.D := by
  norm_num [params, SelectedTranscriptParams.params, SelectedTranscriptParams.D]

private theorem byte_eval_state (H : Bytes → State) (i : Nat)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    (eval H (LiteralByteSampler.samp i P m).toProgram).2.2 =
      (eval (fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
        (LiteralTranscript.samp i P m).toProgram).2.2 := by
  have h := LiteralByteSampler.eval_eq H i P m
  simpa [AspisV8R19.OracleProgramOps.mapView] using
    congrArg (fun z => z.2.2) h

/-- At an ordinary payload row, the successor-state component is exactly the
state stored by the final advance address. -/
theorem ordinary_payload_state (H : Bytes → State)
    (P : LiteralTranscript.Prefix) (bytes : SelectedTranscriptParams.Message)
    (i : Nat) (hi0 : i ≠ 0) (hi26 : i ≠ 26) (hi31 : i ≠ 31) :
    (eval H (LiteralByteSampler.samp i P (.payload bytes)).toProgram).2.2 =
      H ((advanceA params (H ((UnifiedSampler.absorb params i (LiteralTranscript.erasePrefix P) bytes).toBytes))).toBytes) := by
  rw [byte_eval_state]
  change (eval (fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
    (UnifiedSampler.samp params params_D i (LiteralTranscript.erasePrefix P)
      (.payload bytes)).toProgram).2.2 = _
  rw [UnifiedSampler.row_ordinary params params_D i hi0 hi26 hi31
    (LiteralTranscript.erasePrefix P) bytes]
  rw [DuplexSamplers.plain_eval]
  rfl

/-- Row 26 includes its reseed read after the ordinary advance. -/
theorem reseed_payload_state (H : Bytes → State)
    (P : LiteralTranscript.Prefix) (bytes : SelectedTranscriptParams.Message) :
    (eval H (LiteralByteSampler.samp 26 P (.payload bytes)).toProgram).2.2 =
      H ((OpeningReseedFrame.addr (L := SelectedTranscriptParams.L)
        (LiteralTranscript.erasePrefix P).statement.tag
        (by norm_num [SelectedTranscriptParams.L])
        (H ((advanceA params (H ((UnifiedSampler.absorb params 26 (LiteralTranscript.erasePrefix P) bytes).toBytes))).toBytes))).toBytes) := by
  rw [byte_eval_state]
  change (eval (fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
    (UnifiedSampler.samp params params_D 26 (LiteralTranscript.erasePrefix P)
      (.payload bytes)).toProgram).2.2 = _
  rw [UnifiedSampler.row_reseed params params_D (LiteralTranscript.erasePrefix P) bytes]
  rw [DuplexSamplers.reseeded_eval]
  rfl

/-- Row 31 returns the query scanner's selected advance-state component.  The
sampler still evaluates its full paired chain; this result is not asserted to
be the final eighth advance. -/
theorem query_payload_state (H : Bytes → State)
    (P : LiteralTranscript.Prefix) (bytes : SelectedTranscriptParams.Message) :
    (eval H (LiteralByteSampler.samp 31 P (.payload bytes)).toProgram).2.2 =
      (QueryFirstRead.result params
        (fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
        (QuerySampler.state params
          (fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
          ((fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
            (UnifiedSampler.absorb params 31 (LiteralTranscript.erasePrefix P) bytes)))).2 := by
  rw [byte_eval_state]
  change (eval (fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
    (UnifiedSampler.samp params params_D 31 (LiteralTranscript.erasePrefix P)
      (.payload bytes)).toProgram).2.2 = _
  rw [UnifiedSampler.row_query params params_D (LiteralTranscript.erasePrefix P) bytes]
  rw [QuerySamplerBridge.output]
  rfl

/-- Row zero has the public initialization read, the dedicated row-zero
absorb, and then the advance whose state is returned. -/
theorem initial_state (H : Bytes → State)
    (P : LiteralTranscript.Prefix) (c1 : State) (word : LiteralTranscript.C1Word) :
    (eval H (LiteralByteSampler.samp 0 P (.initial c1 word)).toProgram).2.2 =
      H ((advanceA params
        (H ((PublicInitFrame.row0 params params_D
          (H ((PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1).toBytes))).toBytes))).toBytes) := by
  rw [byte_eval_state]
  change (eval (fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
    (UnifiedSampler.samp params params_D 0 (LiteralTranscript.erasePrefix P)
      (.initial c1)).toProgram).2.2 = _
  rw [UnifiedSampler.row_zero params params_D (LiteralTranscript.erasePrefix P) c1]
  rw [DuplexSamplers.initial_eval]
  rfl

#print axioms ordinary_payload_state
#print axioms reseed_payload_state
#print axioms query_payload_state
#print axioms initial_state

end AspisR1.RawCutLiteralStateSuccessor
end
