import S1ValuesOwnedFrameV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedTotal
open Aeneas Aeneas.Std Result WP ControlFlow AspisS1ValuesOwned
abbrev Buffer := alloc.vec.Vec U8

@[step] theorem read_spec (input : Buffer) (index : Usize)
    (bound : index.val< input.length) :
    read_input input index ⦃ p => p.2=input ⦄ := by
  unfold read_input
  step*

@[step] theorem write_spec (output : Buffer) (index : Usize) (value : U8)
    (bound : index.val<output.length) :
    write_output output index value ⦃ updated => updated.length=output.length ⦄ := by
  unfold write_output
  step* <;> simp_all only [alloc.vec.Vec.set_length]

/-- TOTAL one-byte source step, with range obligations stated on the complete
owned input and output. These include both low and zero-filled high limbs. -/
theorem chunk_step_total (input output : Buffer) (chunk byte : Usize)
    (active : byte.val<16)
    (inputRange : chunk.val*16+16≤ input.length)
    (outputRange : chunk.val*32+32≤output.length) :
    ∃ next updated byte1,
      copy_chunk_loop.body chunk input output byte=ok (.cont (next,updated,byte1)) ∧
      next=input ∧ updated.length=output.length ∧ byte1.val=byte.val+1 := by
  have test : byte<16#usize := by scalar_tac
  have hs : copy_chunk_loop.body chunk input output byte ⦃ r =>
      ∃ next updated byte1, r=.cont (next,updated,byte1) ∧
        next=input ∧ updated.length=output.length ∧ byte1.val=byte.val+1 ⦄ := by
    unfold copy_chunk_loop.body
    simp only [if_pos test]
    step* <;> scalar_tac
  obtain ⟨r,call,next,updated,byte1,hr,rest⟩ := spec_imp_exists hs
  subst r
  exact ⟨next,updated,byte1,call,rest⟩

#print axioms read_spec
#print axioms write_spec
#print axioms chunk_step_total
end AspisS1ValuesOwnedTotal
