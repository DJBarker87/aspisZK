import AspisR614SelectedCombineBeta.Funs
import AspisV8R19.R624DecoderInnerExecution
import Mathlib.Tactic
import AspisV8R19.SamplerWordRead
import AspisV8R19.R152WrappingBounds
import AspisV8R19.R487ParserScalarMask

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

/-- Complete outer error/state program. Byte reads and the eight updates remain
inside decodeBlock; no full canonical decoding claim follows yet. -/
def decode {N : Usize} (bytes : Slice U8) (out : Array U32 N) :
    Result (core.result.Result Unit AspisR614SelectedCombineBeta.Error × Array U32 N)
  := do
  if N = 0#usize
  then ok (core.result.Result.Err AspisR614SelectedCombineBeta.Error.Length, out)
  else
    let i ← N % 8#usize
    if i != 0#usize
    then ok (core.result.Result.Err AspisR614SelectedCombineBeta.Error.Length, out)
    else
      let i1 := Slice.len bytes
      let i2 ← N / 8#usize
      let i3 ← lift (Std.Usize.wrapping_mul i2 31#usize)
      if i1 != i3
      then ok (core.result.Result.Err AspisR614SelectedCombineBeta.Error.Length, out)
      else
        let ce ← core.slice.Slice.chunks_exact bytes 31#usize
        let (out1, invalid) ←
          runChunks ce.chunks 0#usize out 0#u32
        let i4 ← lift (Std.U32.wrapping_shr invalid 31#u32)
        if i4 != 0#u32
        then ok (core.result.Result.Err AspisR614SelectedCombineBeta.Error.Canonical, out1)
        else ok (core.result.Result.Ok (), out1)


theorem loop_chunks_exact {N : Usize} (ce : core.slice.iter.ChunksExact U8)
    (out : Array U32 N) (invalid : U32) :
    query_arithmetic.r55_decode_into_loop0 {iter := ce, count := 0#usize} out invalid =
      runChunks ce.chunks 0#usize out invalid := by
  cases ce with
  | mk chunks remainder => exact outer_loop_exact chunks remainder 0#usize out invalid

/-- All inputs, including wrong lengths, noncanonical data, failures and
partially advanced output arrays; no success premise. -/
theorem decoder_outer_exact {N : Usize} (bytes : Slice U8) (out : Array U32 N) :
    query_arithmetic.r55_decode_into bytes out = decode bytes out := by
  simp only [query_arithmetic.r55_decode_into, decode,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, bind_tc_ok, loop_chunks_exact]

/-- Eight bytes read at the source's four exact offsets within a 31-byte chunk. -/
def eight (b : Array U8 31#usize) (i : Nat) (hi : i ≤ 23) : Array U8 8#usize :=
  ⟨(b.val.drop i).take 8, by
    have hb : b.val.length = 31 := b.property
    simp only [List.length_take, List.length_drop, hb]
    change min 8 (31-i) = 8
    omega⟩

theorem read_chunk_success {N : Usize} (b : Array U8 31#usize)
    (i : Usize) (hi : i.val ≤ 23) :
    @query_arithmetic.r55_decode_into.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call
      N (Array.to_slice b) i =
      .ok (core.num.U64.from_le_bytes (eight b i.val hi)) := by
  let finish := SamplerWordRead.small (i.val + 8) (by omega)
  have hchecked : (i + 8#usize : Result Usize) = .ok finish := by
    change UScalar.tryMk .Usize (i.val + 8) = _
    exact SamplerWordRead.try_small _ _
  have hbound : i.val + (8#usize : Usize).val ≤ Usize.max := by
    have := Usize.cMax_bound
    scalar_tac
  have hwrap : Std.Usize.wrapping_add i 8#usize = finish := by
    have h := R152WrappingBounds.checked_add_eq_wrapping i 8#usize hbound
    rw [hchecked] at h
    injection h with he
    exact he.symm
  have hs : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) (Array.to_slice b)
      {start := i, «end» := finish} = .ok (Array.to_slice (eight b i.val hi)) := by
    have hb : b.val.length = 31 := b.property
    simp [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice,
      core.slice.index.SliceIndexRangeUsizeSlice.index, Array.to_slice, Slice.length,
      finish, SamplerWordRead.small_val, eight, List.slice, hb]
    omega
  have hc : core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8
      (Array.to_slice (eight b i.val hi)) = .ok (.Ok (eight b i.val hi)) := by
    simp [core.array.TryFromArrayCopySlice.try_from, Array.to_slice, Slice.length,
      (eight b i.val hi).property]
  simp only [query_arithmetic.r55_decode_into.closure.Insts.CoreOpsFunctionFnTupleUsizeU64.call,
    hwrap, lift, bind_tc_ok, hs, hc, core.result.Result.unwrap]

/-- The selected packed decoder omits the raw-word OR: masked values already
have bit 31 clear. Its actual rejection accumulator still detects exactly P. -/
def packedMaskStep (mask value : U32) : U32 :=
  mask ||| core.num.U32.wrapping_add value 1#u32

theorem packed_step_accepted (mask value : U32) (hv : value.val ≤ 2147483647) :
    R486ParserCanonicalMask.accepted (packedMaskStep mask value).bv ↔
      R486ParserCanonicalMask.accepted mask.bv ∧ value.val < 2147483647 := by
  change R486ParserCanonicalMask.accepted (mask.bv ||| (value.bv + 1#32)) ↔ _
  have hor (x y : BitVec 32) : R486ParserCanonicalMask.accepted (x ||| y) ↔
      R486ParserCanonicalMask.accepted x ∧ R486ParserCanonicalMask.accepted y := by
    unfold R486ParserCanonicalMask.accepted
    rw [BitVec.ushiftRight_or_distrib, BitVec.or_eq_zero_iff]
  rw [hor, R486ParserCanonicalMask.accepted_iff (value.bv + 1#32)]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hn : (value.bv.toNat + 1) % 4294967296 = value.bv.toNat + 1 :=
    Nat.mod_eq_of_lt (by change value.val + 1 < 4294967296; omega)
  change (R486ParserCanonicalMask.accepted mask.bv ∧
      (value.bv.toNat + 1) % 4294967296 < 2147483648) ↔ _
  rw [hn]
  change (R486ParserCanonicalMask.accepted mask.bv ∧ value.bv.toNat + 1 < 2147483648) ↔
    (R486ParserCanonicalMask.accepted mask.bv ∧ value.bv.toNat < 2147483647)
  constructor
  · rintro ⟨hm, hh⟩
    exact ⟨hm, by omega⟩
  · rintro ⟨hm, hh⟩
    exact ⟨hm, by omega⟩

theorem packed_mask_complete (words : List U32)
    (hwords : ∀ value ∈ words, value.val ≤ 2147483647) :
    R486ParserCanonicalMask.accepted (words.foldl packedMaskStep 0#u32).bv ↔
      ∀ value ∈ words, value.val < 2147483647 := by
  have general (mask : U32) :
      R486ParserCanonicalMask.accepted (words.foldl packedMaskStep mask).bv ↔
        R486ParserCanonicalMask.accepted mask.bv ∧
          ∀ value ∈ words, value.val < 2147483647 := by
    induction words generalizing mask with
    | nil => simp
    | cons head tail ih =>
        have hh : head.val ≤ 2147483647 := hwords head (by simp)
        have ht : ∀ value ∈ tail, value.val ≤ 2147483647 := by
          intro value hv
          exact hwords value (by simp [hv])
        simp only [List.foldl_cons]
        rw [ih ht, packed_step_accepted mask head hh]
        simp only [List.mem_cons, forall_eq_or_imp]
        tauto
  rw [general]
  exact and_iff_right R486ParserCanonicalMask.zero_accepted

/-- The exact eight U64 extraction expressions from a complete source chunk. -/
def blockValues (b : Array U8 31#usize) : Array U64 8#usize :=
  let w0 := core.num.U64.from_le_bytes (eight b 0 (by omega))
  let w1 := core.num.U64.from_le_bytes (eight b 8 (by omega))
  let w2 := core.num.U64.from_le_bytes (eight b 16 (by omega))
  let w3 := Std.U64.wrapping_shr
    (core.num.U64.from_le_bytes (eight b 23 (by omega))) 8#u32
  Array.make 8#usize [w0, Std.U64.wrapping_shr w0 31#u32,
    Std.U64.wrapping_shr w0 62#u32 ||| Std.U64.wrapping_shl w1 2#u32,
    Std.U64.wrapping_shr w1 29#u32,
    Std.U64.wrapping_shr w1 60#u32 ||| Std.U64.wrapping_shl w2 4#u32,
    Std.U64.wrapping_shr w2 27#u32,
    Std.U64.wrapping_shr w2 58#u32 ||| Std.U64.wrapping_shl w3 6#u32,
    Std.U64.wrapping_shr w3 25#u32]

theorem block_execution {N : Usize} (block : Usize) (b : Array U8 31#usize)
    (out : Array U32 N) (invalid : U32) :
    decodeBlock block (Array.to_slice b) out invalid =
      R624DecoderInnerExecution.wordRun block (blockValues b) 8
        {start := 0#usize, «end» := 8#usize} out invalid := by
  have h0 := @read_chunk_success N b 0#usize (by decide)
  have h8 := @read_chunk_success N b 8#usize (by decide)
  have h16 := @read_chunk_success N b 16#usize (by decide)
  have h23 := @read_chunk_success N b 23#usize (by decide)
  simp only [decodeBlock, h0, h8, h16, h23, bind_tc_ok, lift]
  rw [R624DecoderInnerExecution.loop_exec_eight]
  rfl

#print axioms block_execution

#print axioms packed_step_accepted
#print axioms packed_mask_complete

#print axioms read_chunk_success

#print axioms decoder_outer_exact

#print axioms body_nil
#print axioms body_cons
#print axioms outer_loop_exact
end AspisV8R19.R623PackedDecoderExecution
