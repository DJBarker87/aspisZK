import F3L_SamplerAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_SamplerMessages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem entry (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (pub : LiteralTranscript.Public) (n row : Nat) (below : row<n) :
    ∃ c,(eval H (F3J_SamplerRun.program pf 0 n (FS.emptyPrefix pub))).2.rounds[row]?=
      some (pf row,c) := by
  have total : row+(n-row-1+1)=n := by omega
  have e := F3L_SamplerAt.entry H pf 0 row (n-row-1) (FS.emptyPrefix pub)
  simp only [FS.emptyPrefix,List.length_nil,Nat.zero_add,total] at e
  exact ⟨_,e⟩

#print axioms entry
end AspisR1.F3L_SamplerMessages
end
