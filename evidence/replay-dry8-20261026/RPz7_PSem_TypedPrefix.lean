import RPz7_PSem_SourceCuts
import ExtractedPrefixTypedFull
set_option autoImplicit false
namespace AspisR1.PSem_TypedPrefix
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

def completedRecords (pre : r1_wire.Prefix) : List SemanticRecordCodec.Bytes :=
  (pre.records.val.take 25).map (fun frame => frame.val.map ExtractedRecordByteValue.rawByte)

theorem typed_prefix (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) :
    ∃ values : SemanticPrefixCodec.Full,
      SemanticPrefixCodec.decodeFull (completedRecords pre)=some values ∧
      SemanticPrefixCodec.encodeFull values=completedRecords pre ∧
      SemanticPrefixCodec.decodeFrom 0 (completedRecords pre)=
        some (SemanticPrefixCodec.entriesOf values) := by
  simpa only [completedRecords,ExtractedPrefixTypedFull.completedRecords,PrefixAdapter.toOld] using
    ExtractedPrefixTypedFull.parse_decodeFull bytes (PrefixAdapter.toOld pre)
      (PrefixAdapter.parse_success bytes pre parsed)

theorem record_count (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) :
    pre.records.val.length=27 := by
  obtain ⟨_,finish,chain,_⟩ := ExtractedPrefixParse.parse_success bytes
    (PrefixAdapter.toOld pre) (PrefixAdapter.parse_success bytes pre parsed)
  exact chain.length

#print axioms typed_prefix
#print axioms record_count
end AspisR1.PSem_TypedPrefix
