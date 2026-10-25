import ExtractedRecordByteValue
import R1SemanticCoefficientCodec

/-! Shared strict low-wide chunk codec. These definitions and algebraic
proofs are moved unchanged from the source-parser consumers so the actual
semantic decoder can share them without importing a second extracted parser
and its unrelated generated instances. -/
namespace AspisR1.ExtractedRecordStrictLow
def zeroLimb : RetainedFieldByteCodec.M31Value := ⟨0, by decide⟩
end AspisR1.ExtractedRecordStrictLow

namespace AspisR1.ExtractedPrefixStrictPayload
open Aeneas Aeneas.Std
open ExtractedRecordByteValue ExtractedRecordStrictLow
open RetainedFieldByteCodec StrictWideByteCodec

/-- A fixed byte carrier, strict decode, zero high half, and exact re-encoding. -/
def StrictLowChunk (raw : List U8) : Prop :=
  ∃ bytes : WideBytes, List.ofFn bytes = raw.map rawByte ∧
    ∃ lo : QM31Limbs,
      decodeWideLE bytes = some (lo, fun _ => zeroLimb) ∧
      List.ofFn (encodeWideLE (lo, fun _ => zeroLimb)) = raw.map rawByte

end AspisR1.ExtractedPrefixStrictPayload

namespace AspisR1.ExtractedPrefixSemanticLow
open Aeneas Aeneas.Std
open ExtractedRecordByteValue ExtractedRecordStrictLow
open RetainedFieldByteCodec RetainedExactLimbCodec WideExactLimbCodec
open SemanticCoefficientCodec

theorem pair_high_zero (lo : QM31Limbs) :
    (pairExactEquiv (lo, fun _ => zeroLimb)).im = 0 := by
  change qm31ExactLimbEquiv (fun _ => zeroLimb) = 0
  have hz : m31ResidueEquiv zeroLimb = 0 := by
    change m31ResidueEquiv 0 = 0
    exact map_zero _
  change (⟨⟨m31ResidueEquiv zeroLimb, m31ResidueEquiv zeroLimb⟩,
    ⟨m31ResidueEquiv zeroLimb, m31ResidueEquiv zeroLimb⟩⟩ :
      AspisV8R15.ExactTowerBase.QM31Exact) = 0
  rw [hz]
  rfl

def lowValue (lo : QM31Limbs) : LowWide :=
  ⟨pairExactEquiv (lo, fun _ => zeroLimb), pair_high_zero lo⟩

/-- The semantic decoder accepts the actual strict chunk with its fixed
canonical-limb field value, and encoding recovers every original byte. -/
theorem strict_chunk_decodeLow (raw : List U8)
    (h : ExtractedPrefixStrictPayload.StrictLowChunk raw) :
    ∃ lo : QM31Limbs,
      decodeLow (raw.map rawByte) = some (lowValue lo) ∧
      encodeLow (lowValue lo) = raw.map rawByte := by
  obtain ⟨bytes, hbytes, lo, hdecode, hencode⟩ := h
  have he : encodeLow (lowValue lo) = raw.map rawByte := by
    change List.ofFn (StrictWideByteCodec.encodeWideLE
      (pairExactEquiv.symm (pairExactEquiv (lo, fun _ => zeroLimb)))) = _
    rw [Equiv.symm_apply_apply]
    exact hencode
  exact ⟨lo, (decodeLow_eq_some_iff _ _).mpr he, he⟩

end AspisR1.ExtractedPrefixSemanticLow

#print axioms AspisR1.ExtractedPrefixSemanticLow.pair_high_zero
#print axioms AspisR1.ExtractedPrefixSemanticLow.strict_chunk_decodeLow
