import AspisR614SelectedCombineBeta.Funs
import Mathlib.Tactic

/-! In-progress actual packed decoder proof. The complete byte-to-canonical
array theorem is not yet proved. This file first binds the complete outer
chunk chronology including enumeration overflow, primitive failure/divergence,
and every inner-loop result. No execution premise or opaque behavior axiom. -/
set_option autoImplicit false
namespace AspisV8R19.R623PackedDecoderExecution
open Aeneas Aeneas.Std Result ControlFlow
open AspisR614SelectedCombineBeta

abbrev ChunkIter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact U8)

def chunkIter (chunks : List (Slice U8)) (rest : Slice U8) (count : Usize) : ChunkIter :=
  {iter := {chunks := chunks, remainder := rest}, count := count}

/-- Exact selected operations for one 31-byte chunk; actual inner loop retained
until its separate byte/array execution theorem is established. -/
def decodeBlock {N : Usize} (block : Usize) (b : Slice U8)
    (out : Array U32 N) (invalid : U32) : Result (Array U32 N × U32) := do
  let w0 ←
    @query_arithmetic.r55_decode_into.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call
      N b 0#usize
  let w1 ←
    @query_arithmetic.r55_decode_into.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call
      N b 8#usize
  let w2 ←
    @query_arithmetic.r55_decode_into.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call
      N b 16#usize
  let i ←
    @query_arithmetic.r55_decode_into.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call
      N b 23#usize
  let w3 ← lift (Std.U64.wrapping_shr i 8#u32)
  let i1 ← lift (Std.U64.wrapping_shr w0 31#u32)
  let i2 ← lift (Std.U64.wrapping_shr w0 62#u32)
  let i3 ← lift (Std.U64.wrapping_shl w1 2#u32)
  let i4 ← lift (i2 ||| i3)
  let i5 ← lift (Std.U64.wrapping_shr w1 29#u32)
  let i6 ← lift (Std.U64.wrapping_shr w1 60#u32)
  let i7 ← lift (Std.U64.wrapping_shl w2 4#u32)
  let i8 ← lift (i6 ||| i7)
  let i9 ← lift (Std.U64.wrapping_shr w2 27#u32)
  let i10 ← lift (Std.U64.wrapping_shr w2 58#u32)
  let i11 ← lift (Std.U64.wrapping_shl w3 6#u32)
  let i12 ← lift (i10 ||| i11)
  let i13 ← lift (Std.U64.wrapping_shr w3 25#u32)
  let (out1, invalid1) ←
    query_arithmetic.r55_decode_into_loop0_loop0
      { start := 0#usize, «end» := 8#usize } out invalid block
      (Array.make 8#usize [ w0, i1, i4, i5, i8, i9, i12, i13 ])
  ok (out1, invalid1)

/-- Structural list program preserving checked enumeration advancement and
all source results. This supplies no success or canonicality assumption. -/
def runChunks {N : Usize} : List (Slice U8) → Usize → Array U32 N → U32 →
    Result (Array U32 N × U32)
  | [], _, out, invalid => .ok (out, invalid)
  | b :: bs, count, out, invalid => do
      let next ← count + 1#usize
      let (out1, invalid1) ← decodeBlock count b out invalid
      runChunks bs next out1 invalid1

theorem body_nil {N : Usize} (rest : Slice U8) (count : Usize)
    (out : Array U32 N) (invalid : U32) :
    query_arithmetic.r55_decode_into_loop0.body
      (chunkIter [] rest count) out invalid = .ok (.done (out, invalid)) := by
  simp [query_arithmetic.r55_decode_into_loop0.body, chunkIter,
    core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.iter.traits.iterator.IteratorChunksExact,
    core.slice.iter.IteratorChunksExact.next]

theorem body_cons {N : Usize} (b : Slice U8) (bs : List (Slice U8))
    (rest : Slice U8) (count : Usize) (out : Array U32 N) (invalid : U32) :
    query_arithmetic.r55_decode_into_loop0.body
      (chunkIter (b :: bs) rest count) out invalid = (do
        let next ← count + 1#usize
        let (out1, invalid1) ← decodeBlock count b out invalid
        ok (.cont (chunkIter bs rest next, out1, invalid1))) := by
  simp only [query_arithmetic.r55_decode_into_loop0.body, chunkIter,
    core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.iter.traits.iterator.IteratorChunksExact,
    core.slice.iter.IteratorChunksExact.next, bind_tc_ok]
  cases hn : count + 1#usize with
  | fail e => simp
  | div => simp
  | ok next => simp [decodeBlock, bind_assoc_eq]

theorem outer_loop_exact {N : Usize} (bs : List (Slice U8))
    (rest : Slice U8) (count : Usize) (out : Array U32 N) (invalid : U32) :
    query_arithmetic.r55_decode_into_loop0 (chunkIter bs rest count) out invalid =
      runChunks bs count out invalid := by
  induction bs generalizing count out invalid with
  | nil =>
      rw [query_arithmetic.r55_decode_into_loop0, loop.eq_def]
      simp only [body_nil, runChunks]
  | cons b bs ih =>
      rw [query_arithmetic.r55_decode_into_loop0, loop.eq_def]
      simp only [body_cons, runChunks]
      cases hn : count + 1#usize with
      | fail e => simp
      | div => simp
      | ok next =>
          simp only [bind_tc_ok]
          cases hd : decodeBlock count b out invalid with
          | fail e => simp
          | div => simp
          | ok pair =>
              rcases pair with ⟨out1, invalid1⟩
              simp only [bind_tc_ok]
              simpa only [query_arithmetic.r55_decode_into_loop0] using
                ih next out1 invalid1

#print axioms body_nil
#print axioms body_cons
#print axioms outer_loop_exact
end AspisV8R19.R623PackedDecoderExecution
