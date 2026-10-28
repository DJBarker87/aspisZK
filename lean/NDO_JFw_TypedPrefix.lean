import NDO_JFw_Prefix
set_option autoImplicit false
namespace AspisR1.JFw_TypedPrefix
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation

theorem inhabited : ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (values : SemanticPrefixCodec.Full),
    compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial =
      ok (.Ok (),expanded) ∧
    AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded = ok (.Ok pre) ∧
    SemanticPrefixCodec.decodeFull (PSem_TypedPrefix.completedRecords pre) = some values ∧
    SemanticPrefixCodec.encodeFull values = PSem_TypedPrefix.completedRecords pre ∧
    SemanticPrefixCodec.decodeFrom 0 (PSem_TypedPrefix.completedRecords pre) =
      some (SemanticPrefixCodec.entriesOf values) := by
  obtain ⟨expanded,pre,expand,parse,_⟩ := JFw_Prefix.inhabited
  obtain ⟨values,decode,encode,entries⟩ := PSem_TypedPrefix.typed_prefix expanded pre parse
  exact ⟨expanded,pre,values,expand,parse,decode,encode,entries⟩

#print axioms inhabited
end AspisR1.JFw_TypedPrefix
