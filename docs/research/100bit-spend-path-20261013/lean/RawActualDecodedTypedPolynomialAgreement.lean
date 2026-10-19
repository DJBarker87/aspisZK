import RawSemanticTypedPolynomialLift
import StrictLowChunkFromTypedDecode

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualDecodedTypedPolynomialAgreement
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualDecodeKTypedCoefficients
open AspisR1PublicPreparation.RawSemanticTypedPolynomialLift
open AspisR1.SemanticCoefficientCodec

/-- Actual decoder success and typed decoding of the same payload imply the
same wide polynomial. Strictness, length, and all value correspondences are
derived, rather than additional caller premises. The typed parse is already
provided by the retained successful Prefix/typed-row parser. -/
theorem actual_decoded_polynomial_eq_typed
    (record : RawActualDecodeKMainAdapter.MainRecord)
    (out : Array MainQM 28#usize) (typed : Coefficients)
    (hactual : RawActualDecodeKMainAdapter.decodeMain
      28#usize record 0#usize = .ok (.Ok out))
    (htyped : decodeCoefficients
      ((payload record).map AspisR1.ExtractedRecordByteValue.rawByte) = some typed) :
    (RawSemanticCheckedStepPolynomialAdapter.exactPolynomial out).map
        (algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact) =
      AspisR1.SemanticCoefficientCodec.polynomial typed := by
  obtain ⟨hlen, hstrict⟩ :=
    AspisR1.StrictLowChunkFromTypedDecode.typed_coefficients_strict _ typed htyped
  obtain ⟨actualTyped, hd, hp⟩ :=
    decodeMain_same_typed_polynomial record out hactual hlen hstrict
  have he : actualTyped = typed := Option.some.inj (hd.symm.trans htyped)
  simpa only [he] using hp

#print axioms actual_decoded_polynomial_eq_typed
end AspisR1PublicPreparation.RawActualDecodedTypedPolynomialAgreement
end
