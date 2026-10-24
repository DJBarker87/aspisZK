import Port4B_PaddingWord

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_Padding
open Aeneas Aeneas.Std Result AspisR1Stage2
open MultiproofConeCanonical

/-- Whole-word coverage, proved symbolically over the physical suffix. -/
theorem chunks_zero (xs : List U8) (whole : xs.length%8=0)
    (all : ∀ c∈(List.toChunksExact 8 (by decide) xs).1, ∀ b∈c, b=0#u8) :
    ∀ b∈xs, b=0#u8 := by
  by_cases short : xs.length<8
  · have empty : xs=[] := List.length_eq_zero_iff.mp (by omega)
    simp only [empty,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  · rw [List.toChunksExact] at all
    simp only [if_neg short] at all
    intro b mem
    have split : b∈xs.take 8 ∨ b∈xs.drop 8 := by
      rw [←List.mem_append,List.take_append_drop];exact mem
    rcases split with front|tail
    · exact all (xs.take 8) (by simp) b front
    · apply chunks_zero (xs.drop 8) (by simp only [List.length_drop];omega)
        (fun c hc => all c (List.mem_cons_of_mem _ hc)) b tail
termination_by xs.length
decreasing_by simp only [List.length_drop];omega

/-- Successful false native padding scan implies exact zero bytes on every
whole eight-byte word. No total error-preserving scan theorem is used. -/
theorem native_zero (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : aspis_core.digest.Digest32 X) (padding : Slice U8)
    (whole : padding.val.length%8=0) (ce after : core.slice.iter.ChunksExact U8)
    (chunks : core.slice.Slice.chunks_exact padding 8#usize=ok ce)
    (scan : (Port3_BatchStd.install base).op0
      (core.iter.traits.iterator.IteratorChunksExact U8)
      (Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
        (Port3_BatchStd.install base) D) ce ()=ok (false,after)) :
    ∀ b∈padding.val, b=0#u8 := by
  have result := Port4B_AnyFalse.all_chunks
    (Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
      (Port3_BatchStd.install base) D) ce.chunks ce.remainder after scan
  unfold core.slice.Slice.chunks_exact at chunks
  split at chunks
  next positive =>
    have same := Result.ok.inj chunks
    subst ce
    apply chunks_zero padding.val whole
    intro c mem
    let view : Slice U8 := ⟨c,by
      have bound := List.toChunksExact_chunk_length (by decide : 0<8) padding.val c mem
      scalar_tac⟩
    have member : view∈(List.toChunksExact 8 (by decide) padding.val).1.attach.map
        (fun c => (⟨c.val,by
          have bound := List.toChunksExact_chunk_length (by decide : 0<8) padding.val c.val c.property
          scalar_tac⟩ : Slice U8)) := by
      apply List.mem_map.mpr
      refine ⟨⟨c,mem⟩,by simp,?_⟩
      exact Subtype.ext rfl
    exact Port4B_PaddingWord.zero_bytes base D view (result.1 view member)
  next impossible => simp at impossible

#print axioms chunks_zero
#print axioms native_zero
end AspisR1.Port4B_Padding
end
