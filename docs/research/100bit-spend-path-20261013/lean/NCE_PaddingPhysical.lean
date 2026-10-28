import NCE_PaddingCuts
import Port4B_SliceReads

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_PaddingPhysical
open Aeneas Aeneas.Std Result NCE_PaddingCuts

/-- Exact chunks exclude the final short remainder. The library's existing
chunk-length bound is only <=8, so derive the exact native domain here. -/
theorem exact_chunk_lengths (xs : List U8) :
    ∀ c ∈ (List.toChunksExact 8 (by decide) xs).1, c.length = 8 := by
  by_cases short : xs.length < 8
  · rw [List.toChunksExact]
    simp only [dif_pos short,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  · rw [List.toChunksExact]
    simp only [dif_neg short]
    intro c mem
    rcases List.mem_cons.mp mem with rfl|tail
    · rw [List.length_take,Nat.min_eq_left (by omega : 8 ≤ xs.length)]
    · exact exact_chunk_lengths (xs.drop 8) c tail
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

/-- The actual physical chunks_exact constructor establishes every local
native predicate's8-byte domain; no chunk list is selected independently. -/
theorem chunk_sizes (padding : Slice U8) (ce : Iter)
    (constructed : core.slice.Slice.chunks_exact padding 8#usize = ok ce) :
    ∀ c ∈ ce.chunks, c.val.length = 8 := by
  unfold core.slice.Slice.chunks_exact at constructed
  split at constructed
  next positive =>
    have same := Result.ok.inj constructed
    subst ce
    intro c mem
    obtain ⟨raw,member,rfl⟩ := List.mem_map.mp mem
    rcases raw with ⟨bytes,rawMember⟩
    exact exact_chunk_lengths padding.val bytes rawMember
  next impossible => simp at impossible

/-- The SAME counted physical suffix supplies padding's partition and length.
This reuses the count scaling/range lemmas; no successful final scan. -/
theorem counted_suffix (nodes : Slice U8) (count : Usize) (capacity : Nat)
    (cap : capacity ≤ 172) (fit : count.val ≤ capacity)
    (size : nodes.val.length = 32*capacity) :
    ∃ padding,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
        nodes {start:=Usize.wrapping_mul 32#usize count} = ok padding ∧
      padding.val = nodes.val.drop (32*count.val) ∧
      padding.val.length = 32*(capacity-count.val) := by
  have scale := Port4B_SliceReads.scaled count (by omega)
  have bound : (Usize.wrapping_mul 32#usize count).val ≤ nodes.val.length := by rw [scale,size]; omega
  refine ⟨Slice.drop nodes (Usize.wrapping_mul 32#usize count),
    MultiproofConeSlices.drop_total nodes _ bound,?_,?_⟩
  · simp only [Slice.drop,scale]
  · simp only [Slice.drop,scale,List.length_drop,size]
    omega

/-- Construct the actual iterator first, derive its domain, THEN consume the
one-native-step induction. The caller Frame may be the full actual Carrier. -/
theorem physical_run {Frame : Type}
    (predicate : core.ops.function.FnMut Unit (Slice U8) Bool) (native : Body Frame)
    (cut : NCE_Native_Padding predicate native) (padding : Slice U8) (frame : Frame) :
    ∃ ce : Iter, core.slice.Slice.chunks_exact padding 8#usize = ok ce ∧
      run native (ce.chunks.length+1) (ce,frame) =
        (do let result ← NBI_Padding.scan predicate ce.remainder ce.chunks
            ok (result.1,result.2,frame)) := by
  have constructed : ∃ ce : Iter, core.slice.Slice.chunks_exact padding 8#usize = ok ce := by
    unfold core.slice.Slice.chunks_exact
    split
    · exact ⟨_,rfl⟩
    · rename_i impossible
      simp at impossible
  obtain ⟨ce,returned⟩ := constructed
  refine ⟨ce,returned,?_⟩
  exact run_eq predicate native cut ce.chunks ce.remainder frame (chunk_sizes padding ce returned)

#print axioms exact_chunk_lengths
#print axioms chunk_sizes
#print axioms counted_suffix
#print axioms physical_run
end AspisR1.NCE_PaddingPhysical
end
