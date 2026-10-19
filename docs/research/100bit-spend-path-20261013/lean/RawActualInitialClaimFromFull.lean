import RawParsedRecordRowReadback
import RawSemanticPrefixMaskClaim
import RawActualInitialMaskRowAgreement

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualInitialClaimFromFull
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter

theorem initial_claim_from_fixed_full
    (pre : r1_wire.Prefix) (values : AspisR1.SemanticPrefixCodec.Full)
    (hfull : AspisR1.SemanticPrefixCodec.encodeFull values =
      PrefixAdapter.completedRecords pre)
    (record : r1_wire.ValidatedRecord) (decoded : Array MainQM 1#usize)
    (initial : MainQM)
    (hrecord : r1_wire.Prefix.validated_record pre 14#u8 = .ok (.Ok record))
    (hdecode : decodeMain 1#usize record 0#usize = .ok (.Ok decoded))
    (hindex : Array.index_usize decoded 0#usize = .ok initial) :
    algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact
      (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe initial)) =
      (AspisR1.RawSemanticPrefixMaskClaim.claimAt14 values).val := by
  have htyped := RawParsedRecordRowReadback.record_decodes_fixed_row
    pre values hfull ⟨14, by omega⟩ 14#u8 record (by rfl) hrecord
  exact RawActualInitialMaskRowAgreement.actual_initial_claim_agrees
    ⟨14, by omega⟩ record decoded initial (values ⟨14, by omega⟩)
    (AspisR1.RawSemanticPrefixMaskClaim.claimAt14 values)
    (AspisR1.RawSemanticPrefixMaskClaim.claimAt14_payload values)
    hdecode hindex htyped

/-- Accepted strict parsing chooses the same typed Full view used to identify
the actual source initial mask-sum claim. No payload or value equality is an
independent premise. -/
theorem initial_claim_from_parse
    (bytes : Slice U8) (pre : r1_wire.Prefix)
    (hparse : PrefixAdapter.parseAccepted bytes = .ok (.Ok pre))
    (record : r1_wire.ValidatedRecord) (decoded : Array MainQM 1#usize)
    (initial : MainQM)
    (hrecord : r1_wire.Prefix.validated_record pre 14#u8 = .ok (.Ok record))
    (hdecode : decodeMain 1#usize record 0#usize = .ok (.Ok decoded))
    (hindex : Array.index_usize decoded 0#usize = .ok initial) :
    ∃ values : AspisR1.SemanticPrefixCodec.Full,
      AspisR1.SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre ∧
      algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact
        (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe initial)) =
        (AspisR1.RawSemanticPrefixMaskClaim.claimAt14 values).val := by
  obtain ⟨values, _hd, hfull, _he⟩ := PrefixAdapter.parse_typedFull bytes pre hparse
  exact ⟨values,hfull,initial_claim_from_fixed_full
    pre values hfull record decoded initial hrecord hdecode hindex⟩

#print axioms initial_claim_from_fixed_full
#print axioms initial_claim_from_parse
end AspisR1PublicPreparation.RawActualInitialClaimFromFull
end
