import AspisV8R19.R448RefillSourceLimb
import AspisV8R19.R460IndexedBlockPermutation
import AspisV8R19.R447SourceInitialBlockLaw

set_option autoImplicit false
namespace AspisV8R19.R462IndexedRefillPermutation
open QM31SamplerProgram DuplexFreshPair R442RejectionAlphabet
open R445InitialBlockRejectionLaw R447SourceInitialBlockLaw
open R448RefillSourceLimb R460IndexedBlockPermutation
abbrev State := SourceDuplexStep.State
abbrev Bytes := DuplexFrames.Bytes

noncomputable def reindex (σ : Nat → Equiv.Perm (Fin modulus)) (offset : Nat)
    (H : Bytes → State) (s : State) : Bytes → State :=
  pairEquiv (DuplexFrames.squeeze (SourceDuplexStep.bytes s))
    (DuplexFrames.advance (SourceDuplexStep.bytes s))
    (indexedBlockPerm σ offset) (Equiv.refl State) H

theorem reindexed_step (σ : Nat → Equiv.Perm (Fin modulus)) (offset : Nat)
    (H : Bytes → State) (s : State) :
    SourceDuplexStep.step (reindex σ offset H s) s =
      (indexedBlockPerm σ offset (SourceDuplexStep.step H s).1, (SourceDuplexStep.step H s).2) :=
  SourceDuplexStep.step_under_reindex H s (indexedBlockPerm σ offset) (Equiv.refl State)

/-- Joint refill result: the carry state and stopping index stay fixed;
the block and accepted symbol move by the stated permutation. -/
theorem refill_joint (σ : Nat → Equiv.Perm (Fin modulus)) (offset : Nat) (H : Bytes → State)
    (c : Cursor) (hc : c.index.val = 8) :
    (limbRun (reindex σ offset H c.state) 8 c).1 =
      [(DuplexFrames.squeeze (SourceDuplexStep.bytes c.state),
          indexedBlockPerm σ offset (SourceDuplexStep.step H c.state).1),
       (DuplexFrames.advance (SourceDuplexStep.bytes c.state),
          (SourceDuplexStep.step H c.state).2)] ∧
    (limbRun (reindex σ offset H c.state) 8 c).2.1 =
      Option.map Fin.val (Option.map (σ offset)
        (initialBlockResult (SourceDuplexStep.step H c.state).1)) ∧
    (limbRun (reindex σ offset H c.state) 8 c).2.2.state =
      (limbRun H 8 c).2.2.state ∧
    (limbRun (reindex σ offset H c.state) 8 c).2.2.block =
      indexedBlockPerm σ offset (limbRun H 8 c).2.2.block ∧
    (limbRun (reindex σ offset H c.state) 8 c).2.2.index =
      (limbRun H 8 c).2.2.index := by
  have h := limbRun_refill_scanAt H 7 c hc (by omega)
  have h' := limbRun_refill_scanAt (reindex σ offset H c.state) 7 c hc (by omega)
  rw [reindexed_step] at h'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h'.1]
    simp only [SourceDuplexStep.calls, reindexed_step]
  · rw [h'.2.1, initial_scan_value, indexedBlock_result]
  · exact h'.2.2.1.trans h.2.2.1.symm
  · exact h'.2.2.2.1.trans (congrArg (indexedBlockPerm σ offset) h.2.2.2.1.symm)
  · apply Fin.ext
    rw [h'.2.2.2.2, h.2.2.2.2, indexedBlock_count]

theorem reindex_preserves_prefix (σ : Nat → Equiv.Perm (Fin modulus)) (offset : Nat)
    (next : List (Bytes × State) → Bytes) (H : Bytes → State) (n : Nat)
    (s : State)
    (fresh : DuplexFrames.Fresh
      ((AspisV8R17.AdaptiveOracle.run next H n []).map Prod.fst)
      (SourceDuplexStep.bytes s)) :
    AspisV8R17.AdaptiveOracle.run next (reindex σ offset H s) n [] =
      AspisV8R17.AdaptiveOracle.run next H n [] := by
  apply pair_preserves_trace
  · exact SourceDuplexStep.unread_squeeze _ s fresh
  · exact SourceDuplexStep.unread_advance _ s fresh

#print axioms reindex_preserves_prefix
#print axioms reindexed_step
#print axioms refill_joint
end AspisV8R19.R462IndexedRefillPermutation
