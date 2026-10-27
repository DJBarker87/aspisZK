import RPz7_F3K_SamplerProtocol
import F3_Model
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_SamplerPrefix
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem raw (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) :
    (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) pub pf)).1 =
      (eval H (F3J_SamplerRun.program pf 0 33 (FS.emptyPrefix pub))).1 := by
  rw [RawCutProverCompiler.verifier,FS2.verifier_eval,F3K_SamplerProtocol.initial D H pub pf 33]
  rfl

/-- Every complete frozen3 model run has exactly its sampler as initial log,
including rejecting executions. Its effectful decision remains in the suffix. -/
theorem model (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input) :
    ∃ tail, (eval H (F3_Model.verifier D i)).1 =
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1 ++ tail := by
  rw [F3_Model.complete_schedule,F3K_SamplerProtocol.initial D H i.semantic.value i.proof 33]
  exact ⟨_,rfl⟩

#print axioms raw
#print axioms model
end AspisR1.ARQ_SamplerPrefix
end
