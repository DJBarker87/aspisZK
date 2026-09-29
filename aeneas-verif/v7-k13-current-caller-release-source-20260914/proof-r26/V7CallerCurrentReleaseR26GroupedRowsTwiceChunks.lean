import V7CallerCurrentReleaseR26GroupedRowsTwiceBasis

/-!
# The four released sixteen-row chunks

The fused grouped helper consumes the fixed sixty-four row schedule four
chunks at a time.  These declarations expose that exact iterator without
reducing any field arithmetic.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceChunks

open V7CallerCurrentReleaseR26GroupedRows

def chunk0 : Slice Std.U8 :=
  ⟨[0#u8, 0#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8], by scalar_tac⟩

def chunk1 : Slice Std.U8 :=
  ⟨[1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 2#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8], by scalar_tac⟩

def chunk2 : Slice Std.U8 :=
  ⟨[1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 2#u8,
    0#u8, 2#u8, 0#u8, 1#u8], by scalar_tac⟩

def chunk3 : Slice Std.U8 :=
  ⟨[1#u8, 3#u8, 3#u8, 3#u8,
    3#u8, 4#u8, 5#u8, 6#u8,
    6#u8, 6#u8, 6#u8, 6#u8,
    6#u8, 6#u8, 6#u8, 6#u8], by scalar_tac⟩

def explicitIterator : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := [chunk0, chunk1, chunk2, chunk3]
    remainder := ⟨[], by scalar_tac⟩ }

def generatedIterator : core.slice.iter.ChunksExact Std.U8 :=
  let source := alloc.vec.Vec.deref releasedRowGroups64
  let positive : (16#usize).val > 0 := by scalar_tac
  let result := List.toChunksExact (16#usize).val positive source.val
  let chunks := result.1.attach.map fun ⟨chunk, member⟩ =>
    ⟨chunk, by
      have := List.toChunksExact_chunk_length positive source.val chunk member
      scalar_tac⟩
  { chunks
    remainder := ⟨result.2, by
      have := List.toChunksExact_remainder_length positive source.val
      scalar_tac⟩ }

private theorem chunkLists (positive : 0 < (16#usize).val) :
    List.toChunksExact (16#usize).val positive releasedRowGroups64.val =
      ([chunk0.val, chunk1.val, chunk2.val, chunk3.val], []) := by
  have proofEq : positive = (by scalar_tac : 0 < (16#usize).val) :=
    Subsingleton.elim _ _
  subst positive
  simp [releasedRowGroups64, chunk0, chunk1, chunk2, chunk3,
    List.toChunksExact]

theorem released_chunks_exact :
    core.slice.Slice.chunks_exact (alloc.vec.Vec.deref releasedRowGroups64)
        16#usize = ok generatedIterator := by
  unfold core.slice.Slice.chunks_exact
  rw [dif_pos (by scalar_tac)]
  rfl

private theorem generatedChunkValues :
    generatedIterator.chunks.map (fun chunk => chunk.val) =
      [chunk0.val, chunk1.val, chunk2.val, chunk3.val] := by
  unfold generatedIterator
  have chunks := congrArg (fun pair => pair.1)
    (chunkLists (by scalar_tac : 0 < (16#usize).val))
  simpa [alloc.vec.Vec.deref] using chunks

private theorem generatedRemainder : generatedIterator.remainder.val = [] := by
  unfold generatedIterator
  have remainder := congrArg (fun pair => pair.2)
    (chunkLists (by scalar_tac : 0 < (16#usize).val))
  simpa [alloc.vec.Vec.deref] using remainder

private theorem sliceListVal_injective {T : Type}
    {left right : List (Slice T)}
    (sameValues : left.map (fun slice => slice.val) =
      right.map (fun slice => slice.val)) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail induction =>
      cases right with
      | nil => simp at sameValues
      | cons head' tail' =>
          simp only [List.map_cons, List.cons.injEq] at sameValues
          obtain ⟨sameHead, sameTail⟩ := sameValues
          have headEq : head = head' := by
            apply Subtype.ext
            exact sameHead
          rw [headEq]
          exact congrArg (List.cons head') (induction sameTail)

private theorem chunksExact_ext {T : Type}
    {left right : core.slice.iter.ChunksExact T}
    (sameChunks : left.chunks = right.chunks)
    (sameRemainder : left.remainder = right.remainder) : left = right := by
  cases left
  cases right
  simp_all

theorem generated_iterator_exact : generatedIterator = explicitIterator := by
  apply chunksExact_ext
  · apply sliceListVal_injective
    rw [generatedChunkValues]
    rfl
  · apply Subtype.ext
    exact generatedRemainder

theorem released_chunks_exact_explicit :
    core.slice.Slice.chunks_exact (alloc.vec.Vec.deref releasedRowGroups64)
        16#usize = ok explicitIterator := by
  rw [released_chunks_exact, generated_iterator_exact]

#print axioms released_chunks_exact_explicit

end V7CallerCurrentReleaseR26GroupedRowsTwiceChunks
