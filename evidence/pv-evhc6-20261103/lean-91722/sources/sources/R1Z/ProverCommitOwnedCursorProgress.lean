import R1Z.ProverCommitOwnedProgress
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R0Z.FsStatement
open R1Z.ProverCommitStepLoop (State)
open R1Z.ProverCommitStreamSource (Bytes32 blockSlices)

/-- Every successful extracted next-word transition consumes exactly one word
inside the allocated finite stream. Counter wrapping is excluded by its bound. -/
theorem next_progress {blocks : Nat} (answers : Fin blocks → OracleAnswer)
    (domain : Slice U8) (state after : State) (value : U32)
    (capacity : blocks < 2^64) (before : valid blocks state)
    (success : prover_commit_reference.next (blockHash answers) domain state = ok (value, after)) :
    valid blocks after ∧ position after = position state + 1 := by
  rw [next_factor] at success
  obtain ⟨triple, filled, rest⟩ := bind_success _ _ _ success
  rcases triple with ⟨counter, block, slot⟩
  simp only [Aeneas.Std.uncurry_apply_pair] at rest
  obtain ⟨loaded, read, result⟩ := bind_success _ _ _ rest
  have same : after = {state with counter := counter, block := block, word := Usize.wrapping_add slot 1#usize} :=
    ((Prod.mk.inj (Result.ok.inj result)).2).symm
  rw [same]
  rcases before with ⟨counterbound, wordbound, empty⟩
  by_cases refill_needed : state.word = 8#usize
  · simp only [refill, refill_needed, if_true] at filled
    obtain ⟨bytes, queried, result⟩ := bind_success _ _ _ filled
    have inbounds : state.counter.val < blocks := by
      by_contra outside
      rw [blockHash_end answers domain state.seed state.counter (by omega)] at queried
      cases queried
    have increment := R1Z.ProverCommitStreamBytes.counter_step state.counter (by omega)
    cases result
    have slotinc := small_increment 0#usize (by decide)
    have slotzero : (0#usize).val = 0 := by scalar_tac
    have oldslot : state.word.val = 8 := by rw [refill_needed]; scalar_tac
    simp only [valid, position, increment, slotinc, slotzero]
    omega
  · simp only [refill, refill_needed, if_false] at filled
    cases filled
    have less : state.word.val < 8 := by scalar_tac
    have inc := small_increment state.word wordbound
    have nonzero : state.counter.val ≠ 0 := by intro h; have := empty h; omega
    simp only [valid, position, inc]
    omega

#print axioms next_progress
end R1Z.ProverCommitOwnedDecoder
