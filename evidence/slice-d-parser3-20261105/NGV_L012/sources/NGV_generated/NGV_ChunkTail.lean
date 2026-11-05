import NGO_ChunksNativeStart
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ChunkTail
theorem exact_chunks {α : Type} (bytes : List α) (n : Nat)
 (lower : 32*n≤bytes.length) (upper : bytes.length<32*(n+1)) :
 List.toChunksExact 32 (by omega) bytes =
 (NGO_ChunkSchedule.windows bytes n, bytes.drop (32*n)) := by
 induction n generalizing bytes with
 | zero =>
   rw [List.toChunksExact.eq_def,dif_pos (by omega)]
   simp [NGO_ChunkSchedule.windows]
 | succ n ih =>
   rw [List.toChunksExact.eq_def,dif_neg (by omega)]
   rw [ih (bytes.drop 32) (by simp only [List.length_drop];omega)
     (by simp only [List.length_drop];omega)]
   simp only [NGO_ChunkSchedule.windows,List.drop_drop]
   congr 2 <;> omega
theorem construct (bytes : Slice U8) :
 ∃ ce : core.slice.iter.ChunksExact U8,
 core.slice.Slice.chunks_exact bytes 32#usize=ok ce ∧
 core.iter.traits.iterator.Iterator.enumerate.trait_default
  (core.iter.traits.iterator.IteratorChunksExact U8) ce =ok {iter:=ce,count:=0#usize} ∧
 ce.chunks.map (fun c=>c.val)=NGO_ChunkSchedule.windows bytes.val (bytes.val.length/32) ∧
 ce.remainder.val=bytes.val.drop (32*(bytes.val.length/32)) := by
 unfold core.slice.Slice.chunks_exact
 simp only [show (32#usize).val>0 by decide,dif_pos]
 refine ⟨_,rfl,rfl,?_,?_⟩
 · simp only [List.map_map,Function.comp_def,List.attach_map_val]
   exact congrArg Prod.fst (exact_chunks bytes.val (bytes.val.length/32) (by omega) (by omega))
 · exact congrArg Prod.snd (exact_chunks bytes.val (bytes.val.length/32) (by omega) (by omega))
#print axioms exact_chunks
#print axioms construct
end NGV_ChunkTail
