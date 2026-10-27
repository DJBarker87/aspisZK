import FJq_SamplerStepErasure
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_SamplerErasure
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
/-- Preserve issued calls, challenges, state and chronological order under
pointwise physical-message equality, without assuming auxiliary word equality. -/
theorem value (H : Bytes → State) (f g : RawCutProverCompiler.Proof)
    (row n : Nat) (P Q : LiteralTranscript.Prefix)
    (samePrefix : LiteralTranscript.erasePrefix P=LiteralTranscript.erasePrefix Q)
    (messages : ∀ k,k<n → LiteralTranscript.erase (f (row+k))=LiteralTranscript.erase (g (row+k))) :
    (eval H (F3J_SamplerRun.program f row n P)).1=
      (eval H (F3J_SamplerRun.program g row n Q)).1 ∧
    LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program f row n P)).2=
      LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program g row n Q)).2 := by
  induction n generalizing row P Q with
  | zero=>exact ⟨rfl,samePrefix⟩
  | succ n ih=>
    have message:=messages 0 (by omega)
    simp only [Nat.add_zero] at message
    have step:=FJq_SamplerStepErasure.value H row P Q (f row) (g row) samePrefix message
    have next : LiteralTranscript.erasePrefix
        (P.ext (f row) (eval H (LiteralByteSampler.samp row P (f row)).toProgram).2)=
        LiteralTranscript.erasePrefix
        (Q.ext (g row) (eval H (LiteralByteSampler.samp row Q (g row)).toProgram).2) := by
      rw [LiteralTranscript.erasePrefix_ext,LiteralTranscript.erasePrefix_ext,samePrefix,message,step]
    have rest:=ih (row+1) _ _ next (by
      intro k hk
      have h:=messages (k+1) (by omega)
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h)
    rw [F3J_SamplerStep.step,F3J_SamplerStep.step]
    refine ⟨?_,rest.2⟩
    rw [rest.1,step]
#print axioms value
end AspisR1.FJq_SamplerErasure
end
