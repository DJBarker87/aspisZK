import RPu_FJc_ByteParser
import RPz7_PSem_Slices
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_FieldBytes
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE wide)
/-- Strict byte-codec VALUE of the original native parser result. -/
theorem parsed (bytes : Slice U8) (out : NE)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes=ok (some out)) :
    FoldedLeafCodec.decodeWide (MultiproofConeCanonical.bytesOf bytes.val)=
      some (AspisR1CurrentWide.Proof.decodeWide (wide out)) := by
  have h := F3P_RecordParsed.parsed bytes (FJc_ByteCarrier.toRecord out)
    (FJc_ByteParser.source bytes out run)
  rw [FJc_ByteCarrier.decoded] at h
  exact h
#print axioms parsed
end AspisR1.FJc_FieldBytes
end
