import RPz7_F3K_SamplerIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_SamplerAt
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Exact interior entry of a run, with the prefix actually fed to its sampler. -/
theorem entry (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row a tail : Nat) (P : LiteralTranscript.Prefix) :
    (eval H (F3J_SamplerRun.program pf row (a+(tail+1)) P)).2.rounds[P.rounds.length+a]?=
      some (pf (row+a),(eval H (LiteralByteSampler.samp (row+a)
        (eval H (F3J_SamplerRun.program pf row a P)).2 (pf (row+a))).toProgram).2) := by
  rw [F3J_SamplerCompose.value H pf row a (tail+1) P]
  have e := F3K_SamplerIndex.first_entry H pf (row+a) tail
    (eval H (F3J_SamplerRun.program pf row a P)).2
  rw [F3J_SamplerRun.length H pf row a P] at e
  exact e

#print axioms entry
end AspisR1.F3L_SamplerAt
end
