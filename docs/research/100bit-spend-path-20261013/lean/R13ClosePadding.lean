import R13CloseLoop
import RecordPayloadPartition
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close.Padding

/-- The source's 32-byte slot/used-prefix arithmetic guarantees that the
8-byte scanner has no ignored short remainder. -/
theorem slot_tail_mod (capacity count : Nat) :
    (32 * capacity - 32 * count) % 8 = 0 := by
  rw [← Nat.mul_sub_left_distrib]
  omega

/-- Actual backend chunks_exact, not a replacement chunk iterator. -/
theorem source_chunks_cover (tail : Slice U8) (chunks : core.slice.iter.ChunksExact U8)
    (hmod : tail.val.length % 8 = 0)
    (h : core.slice.Slice.chunks_exact tail 8#usize = ok chunks) :
    chunks.remainder.val = [] ∧
      (chunks.chunks.map (fun s => s.val)).flatten = tail.val := by
  have hp := AspisR1.RecordPayloadPartition.chunks_cover_of_mod_zero 8 (by decide) tail.val hmod
  unfold core.slice.Slice.chunks_exact at h
  simp only [show (8#usize).val = 8 from rfl, dif_pos (by decide : 8 > 0)] at h
  have he := Result.ok.inj h
  rw [← he]
  constructor
  · exact hp.1
  · simp only [List.map_map, Function.comp_def]
    change ((List.toChunksExact 8 (by decide) tail.val).1.attach.map Subtype.val).flatten = tail.val
    simpa using hp.2

/-- Chunk contents being zero imply every byte in the tail is zero. The
separate source any/word-decoder refinement must establish the premise. -/
theorem covered_zero (tail : Slice U8) (chunks : core.slice.iter.ChunksExact U8)
    (hcover : (chunks.chunks.map (fun s => s.val)).flatten = tail.val)
    (hzero : ∀ chunk ∈ chunks.chunks, ∀ byte ∈ chunk.val, byte = 0#u8) :
    ∀ byte ∈ tail.val, byte = 0#u8 := by
  intro byte hb
  rw [← hcover] at hb
  obtain ⟨bytes, hbytes, hb⟩ := List.mem_flatten.mp hb
  obtain ⟨chunk, hc, he⟩ := List.mem_map.mp hbytes
  exact hzero chunk hc byte (he ▸ hb)

/-- The actual source prefix operation exposes only the selected bytes.
Changing any padding byte after cut cannot affect its argument to verify. -/
theorem source_prefix_exact (stored usedPrefix : Slice U8) (cut : Usize)
    (h : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeToUsizeSlice U8) stored
      { «end» := cut } = ok usedPrefix) : usedPrefix.val = stored.val.take cut.val := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index] at h
  split at h
  · have he := Result.ok.inj h
    have hv := congrArg (fun s : Slice U8 => s.val) he
    simpa only [List.slice, List.drop_zero, Nat.sub_zero] using hv.symm
  · cases h

/-- Missing word-scanner semantics really is a required premise: an
unconstrained scanner returning false need not check zero padding. This is
an interface countermodel, not an accepting frozen-verifier execution. -/
theorem uninterpreted_scan_countermodel :
    ∃ (scan : List U8 → Bool) (bytes : List U8),
      scan bytes = false ∧ ¬ (∀ byte ∈ bytes, byte = 0#u8) := by
  refine ⟨fun _ => false, [1#u8], rfl, ?_⟩
  intro h
  have hf : (1#u8) = 0#u8 := h _ (by simp)
  have hv := congrArg (fun x : U8 => x.val) hf
  contradiction

#print axioms slot_tail_mod
#print axioms source_chunks_cover
#print axioms covered_zero
#print axioms source_prefix_exact
#print axioms uninterpreted_scan_countermodel
end AspisR1Stage2.R13Close.Padding
