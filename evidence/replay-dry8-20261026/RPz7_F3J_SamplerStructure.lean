import RPz7_F3J_SamplerStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_SamplerStructure
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem statement (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row n : Nat) (P : LiteralTranscript.Prefix) :
    (eval H (F3J_SamplerRun.program pf row n P)).2.statement=P.statement := by
  induction n generalizing row P with
  | zero => rfl
  | succ n ih =>
    rw [F3J_SamplerStep.step]
    exact ih (row+1) _

theorem pair (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row : Nat) (P : LiteralTranscript.Prefix) :
    eval H (F3J_SamplerRun.program pf row 2 P)=
      let first := eval H (LiteralByteSampler.samp row P (pf row)).toProgram
      let next := P.ext (pf row) first.2
      let second := eval H (LiteralByteSampler.samp (row+1) next (pf (row+1))).toProgram
      (first.1++second.1,next.ext (pf (row+1)) second.2) := by
  simp only [F3J_SamplerRun.program,eval_bind,eval,List.append_nil]

#print axioms statement
#print axioms pair
end AspisR1.F3J_SamplerStructure
end
