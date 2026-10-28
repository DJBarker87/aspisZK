import NDI_TranscriptInit
import R1SemanticPublicCodecComplete
import MultiproofConeCanonical
set_option autoImplicit false
namespace NDI_TranscriptCaller
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeCanonical

theorem initialized_public (publicBytes : Slice U8) (pub : R0P.Public SemanticPublicWire.M31)
    (parsed : SemanticPublicWire.parsePublic (bytesOf publicBytes.val)=some pub) :
    publicBytes.val.length≤1880 := by
  have bound := SemanticPublicCodecComplete.parsed_length_bound (bytesOf publicBytes.val) pub parsed
  simp only [bytesOf,List.length_map] at bound
  omega

#print axioms initialized_public
end NDI_TranscriptCaller
