import RawCutProverCompiler
import AspisRows40Starts

/-! Aspis 40-row recorded experiment: the compiled prover, copy of the parts of
R1's `RawCutProverCompiler` that name R1's 33-row verifier.

R1's `RawCutProverCompiler.verifier D d` is `FS2.verifier
(LiteralByteProtocol.protocol D) (decisionOnBytes d)`; the 40-row verifier is
`AspisRows40.Starts.verifier D d`, the same with `Protocol.protocol D`
(`r := 40`). `experiment`, `experiment_eval`, `Prover`, `RunView`, `Public`
and `Proof` are generic in the verifier and are reused unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.Compiler
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1 RawCutProverCompiler
open CanonicalCutEnrichedTranscript RawCutTranscriptRun

/-- Copy of `RawCutProverCompiler.compiled` with the 40-row verifier. -/
def compiled (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) : Prover :=
  bind (OracleProgramRecording.record (experiment P (AspisRows40.Starts.verifier decoder d))) fun v =>
    Program.done (v.2.1.1, RawCutTranscriptRun.proof (buildWords v) v.2.1.2)

/-- Copy of `RawCutProverCompiler.eval_compiled` (same proof). -/
theorem eval_compiled (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (compiled decoder d buildWords P) =
      let v := eval H (experiment P (AspisRows40.Starts.verifier decoder d))
      (v.1, (v.2.1.1, RawCutTranscriptRun.proof (buildWords v) v.2.1.2)) := by
  rw [compiled, eval_bind, OracleProgramRecording.eval_record]
  simp [eval]

#print axioms eval_compiled

end AspisRec40.Compiler
end
