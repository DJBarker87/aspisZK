import S1OriginalPreparedSourceEmbeddingV1
import ToBytesP6IndexedCarrierBridgeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentCaller.OriginalSerializerInstallation
open AspisR1PublicPreparation

/-- All eight source coordinates are preserved. The target is the unchanged
emitted serializer under its explicit P6 mutable-iterator interpretation. -/
def sourceCarrier (x : aspis_core.field.WideExact) :
    P6ToBytes.IndexedCarrierBridge.SourceWide :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

def sourceBytes (x : aspis_core.field.WideExact) : Result (Array U8 32#usize) :=
  AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes (sourceCarrier x)

def expectedBytes (x : aspis_core.field.WideExact) : Array U8 32#usize :=
  AspisR1WideToBytesIndexedCandidate.expectedBytes
    (P6ToBytes.IndexedCarrierBridge.toIndexed (sourceCarrier x))

/-- TOTAL for every typed eight-limb value, with no canonicality, loop-success
or independent output premise. Rust Std/P6 interpretation remains explicit. -/
theorem sourceBytes_total (x : aspis_core.field.WideExact) :
    sourceBytes x = ok (expectedBytes x) := by
  obtain ⟨out,hs,he,_⟩ :=
    P6ToBytes.IndexedCarrierBridge.source_output_matches_indexed_encoding (sourceCarrier x)
  have hout : out=expectedBytes x := by
    apply Subtype.ext
    exact he
  simpa only [sourceBytes,hout] using hs

/-- The replacement preserves the entire Result, not just accepted outputs. -/
theorem sourceBytes_eq_indexed (x : aspis_core.field.WideExact) :
    sourceBytes x =
      AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact.to_le_bytes
        (P6ToBytes.IndexedCarrierBridge.toIndexed (sourceCarrier x)) := by
  rw [sourceBytes_total,
    AspisR1WideToBytesIndexedCandidate.indexed_candidate_to_le_bytes]
  rfl

def withOriginalSerializer (sampling : PreparedModel.Boundaries) : PreparedModel.Boundaries :=
  {sampling with toBytes:=sourceBytes}

def withIndexedSerializer (sampling : PreparedModel.Boundaries) : PreparedModel.Boundaries :=
  {sampling with toBytes:=(fun x =>
    AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact.to_le_bytes
      (P6ToBytes.IndexedCarrierBridge.toIndexed (sourceCarrier x)))}

/-- Substitution equality permits replacement in ANY enclosing continuation,
including rejection, divergence, scratch updates and subsequent calls. -/
theorem serializer_boundaries_eq (sampling : PreparedModel.Boundaries) :
    withOriginalSerializer sampling=withIndexedSerializer sampling := by
  have h : sourceBytes = (fun x =>
      AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact.to_le_bytes
        (P6ToBytes.IndexedCarrierBridge.toIndexed (sourceCarrier x))) :=
    funext sourceBytes_eq_indexed
  unfold withOriginalSerializer withIndexedSerializer
  rw [h]

/-- Complete enclosing original Prepared.new operation equality, for every
input, without assuming preparation succeeds or any other child is total. -/
theorem originalNew_serializer_eq (sampling : PreparedModel.Boundaries) :
    @OriginalPreparedInstallation.originalNew (withOriginalSerializer sampling)
        AspisS1M31Embedding.Total.embed =
      @OriginalPreparedInstallation.originalNew (withIndexedSerializer sampling)
        AspisS1M31Embedding.Total.embed := by
  rw [serializer_boundaries_eq]

/-- Complete enclosing caller operation equality, retaining the same Ops,
errors, mutable scratch and after-prepare continuation. This compares the
concrete installed serializers; it does not identify arbitrary free callbacks. -/
theorem installOriginal_serializer_eq (ops : Ops) (sampling : PreparedModel.Boundaries) :
    OriginalPreparedInstallation.installOriginal ops (withOriginalSerializer sampling)
        AspisS1M31Embedding.Total.embed =
      OriginalPreparedInstallation.installOriginal ops (withIndexedSerializer sampling)
        AspisS1M31Embedding.Total.embed := by
  rw [serializer_boundaries_eq]

#print axioms sourceBytes_total
#print axioms sourceBytes_eq_indexed
#print axioms serializer_boundaries_eq
#print axioms originalNew_serializer_eq
#print axioms installOriginal_serializer_eq
end AspisR1CurrentCaller.OriginalSerializerInstallation
