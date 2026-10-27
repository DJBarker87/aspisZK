import RPz7_F3J_SamplerCompose
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_SamplerOne
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def next (H : Bytes → State) (pf : RawCutProverCompiler.Proof) (row : Nat)
    (P : LiteralTranscript.Prefix) : LiteralTranscript.Prefix :=
  P.ext (pf row) (eval H (LiteralByteSampler.samp row P (pf row)).toProgram).2

theorem state (H : Bytes → State) (pf : RawCutProverCompiler.Proof) (row : Nat)
    (P : LiteralTranscript.Prefix) :
    UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix (next H pf row P))=
      (eval H (LiteralByteSampler.samp row P (pf row)).toProgram).2.2 := by
  unfold next
  rw [LiteralTranscript.erasePrefix_ext,UnifiedSampler.stateOf_ext]

theorem one (H : Bytes → State) (pf : RawCutProverCompiler.Proof) (row : Nat)
    (P : LiteralTranscript.Prefix) :
    eval H (F3J_SamplerRun.program pf row 1 P)=
      ((eval H (LiteralByteSampler.samp row P (pf row)).toProgram).1,next H pf row P) := by
  simp only [F3J_SamplerRun.program,eval_bind,eval,List.append_nil]
  rfl

#print axioms state
#print axioms one
end AspisR1.F3K_SamplerOne
end
