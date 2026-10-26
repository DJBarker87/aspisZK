import RPz7_F3K_SamplerIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_SamplerPrefix
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw

theorem retained (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row n : Nat) (P : LiteralTranscript.Prefix) :
    (eval H (F3J_SamplerRun.program pf row n P)).2.rounds.take P.rounds.length=P.rounds := by
  apply List.ext_getElem?
  intro j
  by_cases bound : j<P.rounds.length
  · rw [List.getElem?_take]
    simp only [bound,decide_true,Bool.true_and,if_true]
    exact F3K_SamplerIndex.old_index H pf row n P j bound
  · have left : ¬j<((eval H (F3J_SamplerRun.program pf row n P)).2.rounds.take P.rounds.length).length := by
      simp only [List.length_take,F3J_SamplerRun.length]
      omega
    rw [List.getElem?_eq_none_iff.mpr (by omega),List.getElem?_eq_none_iff.mpr (by omega)]

#print axioms retained
end AspisR1.F3M_SamplerPrefix
end
