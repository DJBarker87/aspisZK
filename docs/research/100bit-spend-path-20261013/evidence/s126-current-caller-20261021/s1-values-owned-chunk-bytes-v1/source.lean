import S1ValuesOwnedStepBytesV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedChunkBytes
open Aeneas Aeneas.Std Result ControlFlow AspisS1ValuesOwned
open AspisS1ValuesOwnedChunkFormula

/-- Exact full-buffer content after the actual inner loop, from its own
accepted return. The existing separate theorem supplies totality. -/
theorem chunk_bytes (input original next updated : Buffer) (chunk : Usize)
    (inputRange : chunk.val*16+16 ≤ input.length)
    (outputRange : chunk.val*32+32 ≤ original.length)
    (call : copy_chunk input original chunk=ok (next,updated)) :
    next=input ∧ updated.length=original.length ∧ Partial input original updated chunk.val 16 := by
  change copy_chunk_loop input original chunk 0#usize=ok (next,updated) at call
  unfold copy_chunk_loop at call
  apply AspisS1LoopSafety.accepted
    (fun (i,o,b) => copy_chunk_loop.body chunk i o b)
    (fun (i,o,b) => i=input ∧ o.length=original.length ∧ b.val≤16 ∧
      Partial input original o chunk.val b.val)
    (fun (i,o) => i=input ∧ o.length=original.length ∧ Partial input original o chunk.val 16)
    _ (input,original,0#usize) ⟨rfl,rfl,by scalar_tac,initial input original chunk.val⟩
    (next,updated) call
  intro state inv r step
  rcases state with ⟨i,o,b⟩
  rcases inv with ⟨sameInput,sameLength,byteBound,held⟩
  subst i
  have outputBound : chunk.val*32+32 ≤ o.length := by rw [sameLength];exact outputRange
  by_cases active : b.val<16
  · obtain ⟨i1,o1,b1,source,_,_,_⟩ :=
      AspisS1ValuesOwnedTotal.chunk_step_total input o chunk b active inputRange outputBound
    have same : r=.cont (i1,o1,b1) := Result.ok.inj (step.symm.trans source)
    subst r
    obtain ⟨inputKept,lengthKept,advanceByte,writes⟩ :=
      AspisS1ValuesOwnedStepBytes.step_bytes input o i1 o1 chunk b b1 active inputRange outputBound source
    refine ⟨inputKept,lengthKept.trans sameLength,by omega,?_⟩
    rw [advanceByte]
    exact advance input original o o1 chunk.val b.val active held writes
  · have test : ¬b<16#usize := by scalar_tac
    unfold copy_chunk_loop.body at step
    simp only [if_neg test] at step
    have same := Result.ok.inj step
    subst r
    have lastByte : b.val=16 := by omega
    exact ⟨rfl,sameLength,by simpa only [lastByte] using held⟩

#print axioms chunk_bytes
end AspisS1ValuesOwnedChunkBytes
