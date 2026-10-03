import AspisV8R19.R448RefillSourceLimb
import AspisV8R19.R449BlockPermutation
import AspisV8R19.R451BlockStoppingPermutation
import AspisV8R19.R447SourceInitialBlockLaw

set_option autoImplicit false
namespace AspisV8R19.R450RefillOraclePermutation
open QM31SamplerProgram DuplexFreshPair R442RejectionAlphabet
open R445InitialBlockRejectionLaw R447SourceInitialBlockLaw
open R448RefillSourceLimb R449BlockPermutation R451BlockStoppingPermutation
abbrev State := SourceDuplexStep.State
abbrev Bytes := DuplexFrames.Bytes

noncomputable def reindex (σ : Equiv.Perm (Fin modulus))
    (H : Bytes → State) (s : State) : Bytes → State :=
  pairEquiv (DuplexFrames.squeeze (SourceDuplexStep.bytes s))
    (DuplexFrames.advance (SourceDuplexStep.bytes s))
    (blockPerm σ) (Equiv.refl State) H

theorem reindexed_step (σ : Equiv.Perm (Fin modulus))
    (H : Bytes → State) (s : State) :
    SourceDuplexStep.step (reindex σ H s) s =
      (blockPerm σ (SourceDuplexStep.step H s).1, (SourceDuplexStep.step H s).2) :=
  SourceDuplexStep.step_under_reindex H s (blockPerm σ) (Equiv.refl State)

/-- Joint refill result: the carry state and stopping index stay fixed;
the block and accepted symbol move by the stated permutation. -/
theorem refill_joint (σ : Equiv.Perm (Fin modulus)) (H : Bytes → State)
    (c : Cursor) (hc : c.index.val = 8) :
    (limbRun (reindex σ H c.state) 8 c).1 =
      [(DuplexFrames.squeeze (SourceDuplexStep.bytes c.state),
          blockPerm σ (SourceDuplexStep.step H c.state).1),
       (DuplexFrames.advance (SourceDuplexStep.bytes c.state),
          (SourceDuplexStep.step H c.state).2)] ∧
    (limbRun (reindex σ H c.state) 8 c).2.1 =
      Option.map Fin.val (Option.map σ
        (initialBlockResult (SourceDuplexStep.step H c.state).1)) ∧
    (limbRun (reindex σ H c.state) 8 c).2.2.state =
      (limbRun H 8 c).2.2.state ∧
    (limbRun (reindex σ H c.state) 8 c).2.2.block =
      blockPerm σ (limbRun H 8 c).2.2.block ∧
    (limbRun (reindex σ H c.state) 8 c).2.2.index =
      (limbRun H 8 c).2.2.index := by
  have h := limbRun_refill_scanAt H 7 c hc (by omega)
  have h' := limbRun_refill_scanAt (reindex σ H c.state) 7 c hc (by omega)
  rw [reindexed_step] at h'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h'.1]
    simp only [SourceDuplexStep.calls, reindexed_step]
  · rw [h'.2.1, initial_scan_value, initialBlockResult_blockPerm]
  · exact h'.2.2.1.trans h.2.2.1.symm
  · exact h'.2.2.2.1.trans (congrArg (blockPerm σ) h.2.2.2.1.symm)
  · apply Fin.ext
    rw [h'.2.2.2.2, h.2.2.2.2, scanAt_count_blockPerm]

theorem reindex_preserves_prefix (σ : Equiv.Perm (Fin modulus))
    (next : List (Bytes × State) → Bytes) (H : Bytes → State) (n : Nat)
    (s : State)
    (fresh : DuplexFrames.Fresh
      ((AspisV8R17.AdaptiveOracle.run next H n []).map Prod.fst)
      (SourceDuplexStep.bytes s)) :
    AspisV8R17.AdaptiveOracle.run next (reindex σ H s) n [] =
      AspisV8R17.AdaptiveOracle.run next H n [] := by
  apply pair_preserves_trace
  · exact SourceDuplexStep.unread_squeeze _ s fresh
  · exact SourceDuplexStep.unread_advance _ s fresh

#print axioms reindex_preserves_prefix
#print axioms reindexed_step
#print axioms refill_joint
end AspisV8R19.R450RefillOraclePermutation
