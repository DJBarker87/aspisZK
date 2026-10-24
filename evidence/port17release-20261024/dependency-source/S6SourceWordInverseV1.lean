import S6FullSourceCodecV1
import S6ByteInverseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6SourceCodec.WordInverse
open AspisS6FiveUnrolledCodec

/-- TOTAL current native field-byte decoder; noncanonical values return none. -/
theorem decode_total (bytes : Array U8 4#usize) :
    ∃ out, aspis_core.field.M31.from_le_bytes bytes=ok out := by
  change ∃ out, (if core.num.U32.from_le_bytes bytes >= aspis_core.field.P
    then ok none else ok (some (core.num.U32.from_le_bytes bytes)))=ok out
  split <;> exact ⟨_,rfl⟩

/-- Accepted bytes are recovered exactly; no independent canonicality premise. -/
theorem accepted_roundtrip (bytes : Array U8 4#usize) (value : U32)
    (h : aspis_core.field.M31.from_le_bytes bytes=ok (some value)) :
    aspis_core.field.M31.to_le_bytes value=ok bytes := by
  change (if core.num.U32.from_le_bytes bytes >= aspis_core.field.P
    then ok none else ok (some (core.num.U32.from_le_bytes bytes)))=ok (some value) at h
  split at h
  · cases h
  · cases h
    change ok (core.num.U32.to_le_bytes (core.num.U32.from_le_bytes bytes))=ok bytes
    rw [AspisS6ByteInverse.u32_to_from]

#print axioms decode_total
#print axioms accepted_roundtrip
end AspisS6SourceCodec.WordInverse
