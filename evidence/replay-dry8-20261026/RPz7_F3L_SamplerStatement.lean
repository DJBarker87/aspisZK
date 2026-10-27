import RPz7_F3J_SamplerStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_SamplerStatement
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem statement (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row n : Nat) (P : LiteralTranscript.Prefix) :
    (eval H (F3J_SamplerRun.program pf row n P)).2.statement=P.statement := by
  induction n generalizing row P with
  | zero => rfl
  | succ n ih =>
    rw [F3J_SamplerStep.step]
    exact ih (row+1) _

#print axioms statement
end AspisR1.F3L_SamplerStatement
end
