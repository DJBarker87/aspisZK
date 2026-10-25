import F3J_SamplerRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_SamplerStep
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem step (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row n : Nat) (P : LiteralTranscript.Prefix) :
    eval H (F3J_SamplerRun.program pf row (n+1) P)=
      let first := eval H (LiteralByteSampler.samp row P (pf row)).toProgram
      let next := eval H (F3J_SamplerRun.program pf (row+1) n (P.ext (pf row) first.2))
      (first.1++next.1,next.2) := by
  rw [F3J_SamplerRun.program,eval_bind]

#print axioms step
end AspisR1.F3J_SamplerStep
end
