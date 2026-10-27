import RPt_FIo_FromBytes
import RPz7_F3P_RecordParsed
set_option autoImplicit false
namespace AspisR1.FJc_ByteCarrier
open FIo_FieldBridge (NE)
abbrev RE := AspisR1RecordParser.field.wide_exact.WideExact
/-- Coordinate-only parser carrier map, preserving all eight raw limbs. -/
def toRecord (x : NE) : RE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
theorem decoded (x : NE) :
    AspisR1CurrentPreparedClaim.Concrete.decode
      (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish
        (AspisR1CurrentWide.Proof.recordWideToFinish (toRecord x)))=
    AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide x) := rfl
#print axioms decoded
end AspisR1.FJc_ByteCarrier
