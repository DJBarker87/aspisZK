import NGO_IteratorStep
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_ChunksNativeStart
/-- Construct the original typed chunks/enumerate iterator from the actual
borrowed slice, with zero count, exact chunk values and no remainder. -/
theorem construct (window : Slice U8) (n : Nat) (length : window.val.length=32*n) :
    ∃ ce : core.slice.iter.ChunksExact U8,
      core.slice.Slice.chunks_exact window 32#usize=ok ce ∧
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorChunksExact U8) ce =
          ok {iter:=ce,count:=0#usize} ∧
      ce.chunks.map (fun chunk=>chunk.val)=NGO_ChunkSchedule.windows window.val n ∧
      ce.remainder.val=[] := by
  unfold core.slice.Slice.chunks_exact
  simp only [show (32#usize).val>0 by decide,dif_pos]
  refine ⟨_,rfl,rfl,?_,?_⟩
  · simp only [List.map_map,Function.comp_def,List.attach_map_val]
    exact congrArg Prod.fst (NGO_ChunkSchedule.exact_chunks window.val n length)
  · exact congrArg Prod.snd (NGO_ChunkSchedule.exact_chunks window.val n length)
#print axioms construct
end NGO_ChunksNativeStart
