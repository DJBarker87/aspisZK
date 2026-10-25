import F3J_SamplerRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_SamplerCompose
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem logs (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row a b : Nat) (P : LiteralTranscript.Prefix) :
    (eval H (F3J_SamplerRun.program pf row (a+b) P)).1=
      (eval H (F3J_SamplerRun.program pf row a P)).1++
      (eval H (F3J_SamplerRun.program pf (row+a) b (eval H (F3J_SamplerRun.program pf row a P)).2)).1 := by
  rw [F3J_SamplerRun.split,eval_bind]

theorem value (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row a b : Nat) (P : LiteralTranscript.Prefix) :
    (eval H (F3J_SamplerRun.program pf row (a+b) P)).2=
      (eval H (F3J_SamplerRun.program pf (row+a) b (eval H (F3J_SamplerRun.program pf row a P)).2)).2 := by
  rw [F3J_SamplerRun.split,eval_bind]

#print axioms logs
#print axioms value
end AspisR1.F3J_SamplerCompose
end
