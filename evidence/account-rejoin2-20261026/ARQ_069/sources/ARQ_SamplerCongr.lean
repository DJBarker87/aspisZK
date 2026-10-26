import F3J_SamplerRun
import F3T_PrefixCongr
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_SamplerCongr
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem run (H : Bytes → State) (pf pg : LiteralProtocol.Proof)
    (row n : Nat) (a b : LiteralTranscript.Prefix)
    (same : ∀ j, j < n → LiteralTranscript.erase (pf (row+j)) = LiteralTranscript.erase (pg (row+j)))
    (initial : LiteralTranscript.erasePrefix a = LiteralTranscript.erasePrefix b) :
    (eval H (F3J_SamplerRun.program pf row n a)).1 =
      (eval H (F3J_SamplerRun.program pg row n b)).1 ∧
    LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf row n a)).2 =
      LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pg row n b)).2 := by
  induction n generalizing row a b with
  | zero => exact ⟨rfl,initial⟩
  | succ n ih =>
    have rows := same 0 (by omega)
    simp only [Nat.add_zero] at rows
    have samp : LiteralByteSampler.samp row a (pf row) = LiteralByteSampler.samp row b (pg row) := by
      unfold LiteralByteSampler.samp LiteralTranscript.samp
      rw [initial,rows]
    simp only [F3J_SamplerRun.program,eval_bind]
    rw [samp]
    have nextInitial : LiteralTranscript.erasePrefix
        (a.ext (pf row) (eval H (LiteralByteSampler.samp row b (pg row)).toProgram).2) =
      LiteralTranscript.erasePrefix
        (b.ext (pg row) (eval H (LiteralByteSampler.samp row b (pg row)).toProgram).2) := by
      rw [LiteralTranscript.erasePrefix_ext,LiteralTranscript.erasePrefix_ext,initial,rows]
    have nextRows : ∀ j, j < n →
        LiteralTranscript.erase (pf (row+1+j)) = LiteralTranscript.erase (pg (row+1+j)) := by
      intro j small
      have h := same (j+1) (by omega)
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using h
    have next := ih (row+1) _ _ nextRows nextInitial
    exact ⟨congrArg (List.append (eval H (LiteralByteSampler.samp row b (pg row)).toProgram).1) next.1,next.2⟩

#print axioms run
end AspisR1.ARQ_SamplerCongr
end
