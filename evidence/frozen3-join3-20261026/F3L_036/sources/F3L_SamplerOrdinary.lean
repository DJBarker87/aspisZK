import F3J_InputRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_SamplerOrdinary
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem initial (H : Bytes → State) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (root : State)
    (erased : LiteralTranscript.erase m=.initial root) :
    ∃ value,(eval H (LiteralByteSampler.samp 0 P m).toProgram).2.1=TranscriptView.Value.ordinary value := by
  rw [LiteralByteSampler.eval_eq]
  change ∃ value,(mapView Addr.toBytes (eval (fun a=>H a.toBytes)
    (UnifiedSampler.samp SelectedTranscriptParams.params _ 0 (LiteralTranscript.erasePrefix P)
      (LiteralTranscript.erase m)).toProgram)).2.1=_
  rw [erased,UnifiedSampler.row_zero,DuplexSamplers.initial_eval]
  exact ⟨_,rfl⟩

theorem payload (H : Bytes → State) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (row : Nat) (positive : row≠0) (notQuery : row≠31)
    (erased : LiteralTranscript.erase m=.payload b) :
    ∃ value,(eval H (LiteralByteSampler.samp row P m).toProgram).2.1=TranscriptView.Value.ordinary value := by
  rw [LiteralByteSampler.eval_eq]
  change ∃ value,(mapView Addr.toBytes (eval (fun a=>H a.toBytes)
    (UnifiedSampler.samp SelectedTranscriptParams.params _ row (LiteralTranscript.erasePrefix P)
      (LiteralTranscript.erase m)).toProgram)).2.1=_
  rw [erased]
  by_cases reseed : row=26
  · subst row
    rw [UnifiedSampler.row_reseed,DuplexSamplers.reseeded_eval]
    exact ⟨_,rfl⟩
  · rw [UnifiedSampler.row_ordinary _ _ row positive reseed notQuery,DuplexSamplers.plain_eval]
    exact ⟨_,rfl⟩

#print axioms initial
#print axioms payload
end AspisR1.F3L_SamplerOrdinary
end
