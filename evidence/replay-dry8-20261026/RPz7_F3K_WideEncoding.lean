import RPz7_F3K_LimbBytes
import RPz7_PAln_InactiveDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_WideEncoding
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller.OriginalSerializerInstallation
open AspisV8R19.SqueezeOracleBridge
open RetainedFieldByteCodec StrictWideByteCodec

def prepFromParsed (x : CandidateWideParserRefinement.Wide) :
    AspisR1PublicPreparation.aspis_core.field.WideExact :=
  AspisR1SelectedWideViewV1.prepCarrier (AspisR1SelectedWideViewV1.parserCarrier x)

theorem encoding (limbs : WideLimbs) :
    MultiproofConeCanonical.bytesOf
      (expectedBytes (prepFromParsed (CandidateWideParserRefinement.limbsToCandidate limbs))).val=
      List.ofFn (encodeWideLE limbs) := by
  change (AspisR1WideToBytesIndexedCandidate.expectedList
    (P6ToBytes.IndexedCarrierBridge.toIndexed (sourceCarrier (prepFromParsed
      (CandidateWideParserRefinement.limbsToCandidate limbs))))).map decodeByte=_
  change ((AspisR1WideToBytesIndexedCandidate.limbBytes (M31ParserRefinement.valueToU32 (limbs.1 0)) ++
    AspisR1WideToBytesIndexedCandidate.limbBytes (M31ParserRefinement.valueToU32 (limbs.1 1)) ++
    AspisR1WideToBytesIndexedCandidate.limbBytes (M31ParserRefinement.valueToU32 (limbs.1 2)) ++
    AspisR1WideToBytesIndexedCandidate.limbBytes (M31ParserRefinement.valueToU32 (limbs.1 3)) ++
    AspisR1WideToBytesIndexedCandidate.limbBytes (M31ParserRefinement.valueToU32 (limbs.2 0)) ++
    AspisR1WideToBytesIndexedCandidate.limbBytes (M31ParserRefinement.valueToU32 (limbs.2 1)) ++
    AspisR1WideToBytesIndexedCandidate.limbBytes (M31ParserRefinement.valueToU32 (limbs.2 2)) ++
    AspisR1WideToBytesIndexedCandidate.limbBytes (M31ParserRefinement.valueToU32 (limbs.2 3))).map decodeByte)=_
  simp only [List.map_append,F3K_LimbBytes.canonical_limb]
  rfl

#print axioms encoding
end AspisR1.F3K_WideEncoding
end
