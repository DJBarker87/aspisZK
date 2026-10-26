import S1ValuesOwnedStepTotalV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedTotal
open Aeneas Aeneas.Std Result ControlFlow AspisS1ValuesOwned

/-- TOTAL actual inner loop. The induction decreases 16-byte, without
normalizing any concrete expanded buffer or recurrence. -/
theorem chunk_loop_total (input output : Buffer) (chunk byte : Usize)
    (inputRange : chunk.val*16+16 ≤ input.length)
    (outputRange : chunk.val*32+32 ≤ output.length) :
    ∃ next updated, copy_chunk_loop input output chunk byte=ok (next,updated) := by
  have aux : ∀ n (input output : Buffer) (byte : Usize), 16-byte.val=n →
      chunk.val*16+16 ≤ input.length → chunk.val*32+32 ≤ output.length →
      ∃ next updated, copy_chunk_loop input output chunk byte=ok (next,updated) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro input output byte measure hi ho
      by_cases active : byte.val<16
      · obtain ⟨next,updated,byte1,step,sameInput,sameLength,advance⟩ :=
          chunk_step_total input output chunk byte active hi ho
        have smaller : 16-byte1.val<n := by omega
        have hi1 : chunk.val*16+16 ≤ next.length := by rw [sameInput];exact hi
        have ho1 : chunk.val*32+32 ≤ updated.length := by rw [sameLength];exact ho
        obtain ⟨finalInput,finalOutput,tail⟩ :=
          ih (16-byte1.val) smaller next updated byte1 rfl hi1 ho1
        refine ⟨finalInput,finalOutput,?_⟩
        unfold copy_chunk_loop at tail ⊢
        unfold loop
        dsimp only
        rw [step]
        exact tail
      · refine ⟨input,output,?_⟩
        have test : ¬byte<16#usize := by scalar_tac
        unfold copy_chunk_loop
        unfold loop
        simp only [copy_chunk_loop.body,if_neg test]
  exact aux (16-byte.val) input output byte rfl inputRange outputRange

theorem chunk_total (input output : Buffer) (chunk : Usize)
    (inputRange : chunk.val*16+16 ≤ input.length)
    (outputRange : chunk.val*32+32 ≤ output.length) :
    ∃ next updated, copy_chunk input output chunk=ok (next,updated) :=
  chunk_loop_total input output chunk 0#usize inputRange outputRange

#print axioms chunk_loop_total
#print axioms chunk_total
end AspisS1ValuesOwnedTotal
