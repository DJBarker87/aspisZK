import S4CanonicalOpeningV1
import S4ScannedOpeningForwardRootV1
import ExtractedRecordByteValue
set_option autoImplicit false
namespace AspisR1.S4ScannedOpeningDecodeV1
open Aeneas Aeneas.Std Result
open AspisR1.MixedLeafDecoder AspisR1.MixedLeafEncoding

theorem scanned_opening_decode (proof : Slice U8) (j : Nat) (q : Slice U8)
    (a : Array U8 608#usize) (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (ha : a.val = q.val.slice 0 (608#usize)) :
    ∃ c1 c2,
      decodeC1 ((a.val.map ExtractedRecordByteValue.rawByte).take 480) = some c1 ∧
      decodeC2 ((a.val.map ExtractedRecordByteValue.rawByte).drop 480) = some c2 ∧
      a.val.map ExtractedRecordByteValue.rawByte = encodeC1 c1 ++ encodeC2 c2 := by
  have hc := AspisR1FastDotsScannedOpeningForwardRootV1.strict_scan_accepted_opening
    proof j q hlen hj hread hscan
  have hp := AspisR1FastDotsCanonicalOpeningForwardRootV1.opening_payload_canonical q a ha hc
  have hb : MultiproofConeCanonical.bytesOf a.val = a.val.map ExtractedRecordByteValue.rawByte := by
    apply List.map_congr_left
    intro b _
    apply Fin.ext
    rfl
  rw [hb] at hp
  exact S4CanonicalOpeningV1.canonical_opening_decode_exists _
    (by simp only [List.length_map]; exact a.property) hp
#print axioms scanned_opening_decode
end AspisR1.S4ScannedOpeningDecodeV1
