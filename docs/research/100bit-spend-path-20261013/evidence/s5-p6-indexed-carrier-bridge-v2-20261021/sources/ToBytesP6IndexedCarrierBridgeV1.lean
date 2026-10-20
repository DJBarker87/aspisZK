import ToBytesP6OutputInvariantV1
import AspisR1WideToBytesIndexedCandidate.ToBytesGeneratedOutputV11
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace P6ToBytes.IndexedCarrierBridge

abbrev SourceWide := AspisR1WideToBytesSource.field.wide_exact.WideExact
abbrev IndexedWide := AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact

def toIndexed (x : SourceWide) : IndexedWide :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

private theorem u32_bytes_as_limbBytes (w : Std.U32) :
    (core.num.U32.to_le_bytes w).val =
      AspisR1WideToBytesIndexedCandidate.limbBytes w := by
  apply List.ext_getElem
  · simp [core.num.U32.to_le_bytes,
      AspisR1WideToBytesIndexedCandidate.limbBytes, Array.length_eq]
  · intro i hleft hright
    have hi : i < 4 := by
      simpa [AspisR1WideToBytesIndexedCandidate.limbBytes] using hright
    cases i with
    | zero => simp [core.num.U32.to_le_bytes,
        AspisR1WideToBytesIndexedCandidate.limbBytes]
    | succ i =>
      cases i with
      | zero => simp [core.num.U32.to_le_bytes,
          AspisR1WideToBytesIndexedCandidate.limbBytes]
      | succ i =>
        cases i with
        | zero => simp [core.num.U32.to_le_bytes,
            AspisR1WideToBytesIndexedCandidate.limbBytes]
        | succ i =>
          cases i with
          | zero => simp [core.num.U32.to_le_bytes,
              AspisR1WideToBytesIndexedCandidate.limbBytes]
          | succ i => omega

theorem serializedWords_eq_indexed_expectedList (x : SourceWide) :
    P6ToBytes.OutputInvariant.serializedWords x =
      AspisR1WideToBytesIndexedCandidate.expectedList (toIndexed x) := by
  simp [P6ToBytes.OutputInvariant.serializedWords,
    P6ToBytes.Steps.sourceLimbs,
    AspisR1WideToBytesIndexedCandidate.expectedList,
    toIndexed, u32_bytes_as_limbBytes, List.append_assoc]

/-- The original emitted serializer's P6-model output agrees with the exact
byte-list interpretation used by the checked indexed candidate theorem. The
indexed candidate is a separate nominal source owner; this theorem compares
outputs through an explicit fieldwise carrier map and does not establish
Rust-stdlib or production-source equivalence. -/
theorem source_output_matches_indexed_encoding (x : SourceWide) :
    ∃ out : Array Std.U8 32#usize,
      AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes x = .ok out ∧
      out.val = (AspisR1WideToBytesIndexedCandidate.expectedBytes (toIndexed x)).val ∧
      AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact.to_le_bytes
        (toIndexed x) = .ok (AspisR1WideToBytesIndexedCandidate.expectedBytes (toIndexed x)) := by
  obtain ⟨out, hsource, hcontents⟩ :=
    P6ToBytes.OutputInvariant.to_le_bytes_output_contents x
  refine ⟨out, hsource, ?_,
    AspisR1WideToBytesIndexedCandidate.indexed_candidate_to_le_bytes (toIndexed x)⟩
  rw [hcontents]
  simp [AspisR1WideToBytesIndexedCandidate.expectedBytes,
    serializedWords_eq_indexed_expectedList]

#print axioms serializedWords_eq_indexed_expectedList
#print axioms source_output_matches_indexed_encoding
end P6ToBytes.IndexedCarrierBridge
