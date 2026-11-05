import NHF_ViewCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHF_ViewDecoder
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1
open StrictWideByteCodec WideParserArrayHalves
/-- The packet law for the cut decoder is total on every original32-byte array;
canonicality/success is decided by the decoder, never a caller premise. -/
theorem result (bytes : Array U8 32#usize) :
 viewFromBytes (Array.to_slice bytes) =
 ok (((decodeWideLE (arrayBytes32 bytes)).map
   CandidateWideParserRefinement.limbsToCandidate).map parserCarrier) := by
 unfold viewFromBytes
 rw [UnrolledWideParserRefinement.source_refines]
 rfl
/-- The exact cut input length follows from offsets independently of decoding. -/
theorem domain : 7527-7495=32 := by decide
#print axioms result
#print axioms domain
end AspisR1.NHF_ViewDecoder
end
