import LogA_Tags
set_option autoImplicit false
namespace AspisR1.LogA_PublicBytes
open AspisV8R19.DuplexFrames

/-- Physical ASF8 bytes cannot be the model's semantic public serialization.
The physical length is a local input condition; this theorem does not construct
native accepted accounts or discharge their source-binding obligation. -/
theorem physical_ne_semantic (physical semantic : Bytes)
    (fullWidth : physical.length = 1880)
    (pub : R0P.Public SemanticPublicWire.M31)
    (parsed : SemanticPublicWire.parsePublic semantic = some pub) :
    physical ≠ semantic := by
  have small := SemanticPublicCodecComplete.parsed_length_bound semantic pub parsed
  intro equal
  rw [← equal,fullWidth] at small
  omega

/-- Changing an appended fixed-width digest field is not merely changing
slice descriptors: it changes the flattened oracle address. -/
theorem changed_digest_changes_address (pre post : Bytes) (a b : Bytes)
    (different : a ≠ b) : pre ++ a ++ post ≠ pre ++ b ++ post := by
  intro equal
  exact different (List.append_cancel_left (List.append_cancel_right equal))

#print axioms physical_ne_semantic
#print axioms changed_digest_changes_address
end AspisR1.LogA_PublicBytes
