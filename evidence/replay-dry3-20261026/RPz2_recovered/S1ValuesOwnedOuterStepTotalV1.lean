import S1ValuesOwnedChunkTotalV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedTotal
open Aeneas Aeneas.Std Result WP ControlFlow AspisS1ValuesOwned

@[step] theorem chunk_spec (input output : Buffer) (chunk : Usize)
    (inputRange : chunk.val*16+16 ≤ input.length)
    (outputRange : chunk.val*32+32 ≤ output.length) :
    copy_chunk input output chunk ⦃ p => p.1=input ∧ p.2.length=output.length ⦄ := by
  obtain ⟨next,updated,call⟩ := chunk_total input output chunk inputRange outputRange
  have framed := AspisS1ValuesOwnedFrame.chunk_frame input output next updated chunk 0#usize call
  rw [call]
  exact framed

/-- TOTAL chunk step with all index arithmetic discharged from the actual
number of chunks and full buffer lengths. -/
theorem outer_step_total (input output : Buffer) (count chunk : Usize)
    (active : chunk.val<count.val)
    (inputRange : count.val*16 ≤ input.length)
    (outputRange : count.val*32 ≤ output.length) :
    ∃ next updated chunk1,
      values_owned_reference_loop.body count input output chunk=ok (.cont (next,updated,chunk1)) ∧
      next=input ∧ updated.length=output.length ∧ chunk1.val=chunk.val+1 := by
  have test : chunk<count := by scalar_tac
  have hs : values_owned_reference_loop.body count input output chunk ⦃ r =>
      ∃ next updated chunk1, r=.cont (next,updated,chunk1) ∧
        next=input ∧ updated.length=output.length ∧ chunk1.val=chunk.val+1 ⦄ := by
    unfold values_owned_reference_loop.body
    simp only [if_pos test]
    step* <;> scalar_tac
  obtain ⟨r,call,next,updated,chunk1,hr,rest⟩ := spec_imp_exists hs
  subst r
  exact ⟨next,updated,chunk1,call,rest⟩

#print axioms chunk_spec
#print axioms outer_step_total
end AspisS1ValuesOwnedTotal
