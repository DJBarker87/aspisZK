import R1Z.ProverCommitOwnedReadBound
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R0Z.FsStatement
open R1Z.ProverCommitStepLoop (State)
open R1Z.ProverCommitStreamSource (Bytes32)

theorem usize_size_lower : 2^32 ≤ UScalar.size .Usize := by
  rw [UScalar.size_def]
  exact Nat.pow_le_pow_right (by decide) System.Platform.le_numBits

theorem small_offset (word : Usize) (bound : word.val < 8) :
    (Usize.wrapping_mul word 4#usize).val ≤ 28 := by
  rw [Usize.wrapping_mul_val_eq]
  have four : (4#usize).val = 4 := by scalar_tac
  have size := usize_size_lower
  rw [four, Nat.mod_eq_of_lt (by omega)]
  omega

theorem offset_add (offset : Usize) (bound : offset.val ≤ 28)
    (amount : Usize) (small : amount.val ≤ 3) :
    (Usize.wrapping_add offset amount).val < 32 := by
  rw [Usize.wrapping_add_val_eq]
  have size := usize_size_lower
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem readBlock_total (block : Bytes32) (word : Usize) (bound : word.val < 8) :
    ∃ value, readBlock block word = ok value := by
  let offset := Usize.wrapping_mul word 4#usize
  have offsetbound : offset.val ≤ 28 := small_offset word bound
  have len : block.length = 32 := by exact block.property
  obtain ⟨b₀, h₀, _⟩ := WP.spec_imp_exists
    (Aeneas.Std.Array.index_usize_spec block offset (by rw [len]; omega))
  obtain ⟨b₁, h₁, _⟩ := WP.spec_imp_exists
    (Aeneas.Std.Array.index_usize_spec block (Usize.wrapping_add offset 1#usize)
      (by rw [len]; exact offset_add offset offsetbound 1#usize (by decide)))
  obtain ⟨b₂, h₂, _⟩ := WP.spec_imp_exists
    (Aeneas.Std.Array.index_usize_spec block (Usize.wrapping_add offset 2#usize)
      (by rw [len]; exact offset_add offset offsetbound 2#usize (by decide)))
  obtain ⟨b₃, h₃, _⟩ := WP.spec_imp_exists
    (Aeneas.Std.Array.index_usize_spec block (Usize.wrapping_add offset 3#usize)
      (by rw [len]; exact offset_add offset offsetbound 3#usize (by decide)))
  dsimp only [offset] at h₀ h₁ h₂ h₃
  simp only [readBlock, h₀, h₁, h₂, h₃, bind_tc_ok]
  exact ⟨_, rfl⟩

/-- If the finite stream has a word remaining, next-word cannot fail or diverge.
This includes the last cached word and the refill boundary. -/
theorem next_total {blocks : Nat} (answers : Fin blocks → OracleAnswer)
    (domain : Slice U8) (state : State) (before : valid blocks state)
    (room : position state < 8*blocks) :
    ∃ value after, prover_commit_reference.next (blockHash answers) domain state = ok (value, after) := by
  rw [next_factor]
  by_cases needed : state.word = 8#usize
  · have inbounds : state.counter.val < blocks := by
      have oldslot : state.word.val = 8 := by rw [needed]; scalar_tac
      unfold position at room
      rw [oldslot] at room
      omega
    obtain ⟨value, read⟩ := readBlock_total (answerBytes (answers ⟨state.counter.val, inbounds⟩))
      0#usize (by decide)
    simp only [refill, needed, if_true, blockHash_at answers domain state.seed state.counter inbounds,
      bind_tc_ok, Aeneas.Std.uncurry_apply_pair, read]
    exact ⟨_, _, rfl⟩
  · have bound : state.word.val < 8 := by
      rcases before with ⟨_, wordbound, _⟩
      scalar_tac
    obtain ⟨value, read⟩ := readBlock_total state.block state.word bound
    simp only [refill, needed, if_false, bind_tc_ok, Aeneas.Std.uncurry_apply_pair, read]
    exact ⟨_, _, rfl⟩

#print axioms usize_size_lower
#print axioms small_offset
#print axioms offset_add
#print axioms readBlock_total
#print axioms next_total
end R1Z.ProverCommitOwnedDecoder
