import S1ValuesOwnedStepTotalV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedCell
open Aeneas Aeneas.Std Result WP AspisS1ValuesOwned
abbrev Buffer := alloc.vec.Vec U8

/-- Every returned mutable byte index uses the actual Vec setter. -/
theorem write_exact (output updated : Buffer) (index : Usize) (value : U8)
    (call : write_output output index value=ok updated) :
    updated=alloc.vec.Vec.set output index value := by
  unfold write_output at call
  simp only [alloc.vec.Vec.index_mut_slice_index,alloc.vec.Vec.index_mut_usize] at call
  cases indexed : alloc.vec.Vec.index_usize output index with
  | fail e => simp only [indexed] at call;cases call
  | div => simp only [indexed] at call;cases call
  | ok old =>
    simp only [indexed,bind_tc_ok] at call
    exact (Result.ok.inj call).symm

theorem read_exact (input next : Buffer) (index : Usize) (value : U8)
    (bound : index.val< input.length)
    (call : read_input input index=ok (value,next)) :
    next=input ∧ value=input.val[index.val] := by
  have hs : read_input input index ⦃ p => p.2=input ∧ p.1=input.val[index.val] ⦄ := by
    unfold read_input
    step*
  obtain ⟨p,hp,facts⟩ := spec_imp_exists hs
  have same := Result.ok.inj (hp.symm.trans call)
  subst p
  exact facts

/-- Exact observed byte after an accepted source setter, for every Nat index,
including indices outside the buffer. -/
theorem write_byte (output updated : Buffer) (index : Usize) (value : U8)
    (bound : index.val<output.length)
    (call : write_output output index value=ok updated) (j : Nat) :
    updated.val[j]?=if j=index.val then some value else output.val[j]? := by
  rw [write_exact output updated index value call]
  change (output.val.set index.val value)[j]?= _
  by_cases same : j=index.val
  · subst j
    simp only [List.getElem?_set_self bound,ite_true]
  · simp only [List.getElem?_set_ne (Ne.symm same),if_neg same]

#print axioms write_exact
#print axioms read_exact
#print axioms write_byte
end AspisS1ValuesOwnedCell
